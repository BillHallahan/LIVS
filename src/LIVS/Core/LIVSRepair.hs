-- | LIVS to repair functions.
-- Unlike the general LIVS algorithm, modifies existing functions and tries to
-- preserve their properties using fault localization
module LIVS.Core.LIVSRepair ( livsRepairCVC4 ) where

import LIVS.Config.Config
import LIVS.Core.Fuzz
import LIVS.Core.LIVS
import LIVS.Core.LIVSSynth

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import qualified LIVS.Language.SubFunctions as Sub
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Language.Monad.Naming

import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.Result

import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface

import Control.Monad.Random
import qualified Data.HashSet as S
import Data.List

livsRepairCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m b -> b -> Fuzz m b -> FilePath -> CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> [Example] -> m (H.Heap, [Id])
livsRepairCVC4 con le b fuzz fp cg const_val = livsRepair con le b (runSygusWithGrammar con cg const_val) fuzz fp cg

livsRepair :: MonadIO m
           => LIVSConfigNames
           -> LanguageEnv m b
           -> b
           -> Gen m
           -> Fuzz m b
           -> FilePath
           -> CallGraph
           -> H.Heap
           -> T.TypeEnv
           -> [Example]
           -> m (H.Heap, [Id])
livsRepair con le b gen fuzz fp cg h tenv exs = do

    -- Get the Id of the function to repair
    let is = nub $ map func exs

    -- Modify call graph so that it only includes the functions for which there is no path to the target function
    let cg' = ( \g@(CallGraph _ _ _ ve) i -> createCallGraph [x | x <- ve, not $ path g (fst x) i] ) cg (head is)

    -- Get definitions for usable component functions
    (h', sub, exs') <- livs con le b gen fuzz fp cg' h tenv
    let exs'' = examplesForFunc (idName (head is)) (exs ++ exs')

    -- Convert the source code for the target function into an Expr
    original_def <- extractDef le fp (idName (head is))

    -- Debugging
    liftIO $ (putStrLn $ "Original function: " ++ toJavaScriptDef S.empty (idName (head is)) original_def)

    let partial_def = mkLams (leadingLams original_def) EmptyExpr

    (h'', is', _) <- livsRepair' con le b gen cg' sub h' tenv exs exs'' is original_def (partial_def, (idType (head is)))
    return (h'', is')

livsRepair' :: MonadIO m
            => LIVSConfigNames
            -> LanguageEnv m b
            -> b
            -> Gen m
            -> CallGraph
            -> Sub.SubFunctions
            -> H.Heap
            -> T.TypeEnv
            -> [Example]
            -> [Example]
            -> [Id]
            -> Expr
            -> (Expr, Type)
            -> m (H.Heap, [Id], Int)
livsRepair' con le b gen cg sub h tenv exs exs' is original_def (partial_def, t) = do

    -- Get I/O constraints and an id for the sub expression to synthesize
    let constraints = map (\(Example i it ot) -> Constraint i it ot partial_def) exs'
    let is' = [Id (idName (head is)) t]

    -- Debugging
    liftIO $ (putStr $ "Repair area: " ++ toJavaScriptDef S.empty (idName (head is)) partial_def)

    -- Synthesize sub expression
    (h', is'') <- callSynthesizer con gen cg sub h tenv constraints is'
    case is'' of
        [] -> return (h', is'', 0) -- Synthesis failed
        _ -> do

            -- Insert the synthesized subexpression into our partial definition to create a full version of the target function
            let sub_def = case H.lookup (idName (head is'')) h' of
                             Just (H.Def e) -> e
                             _ -> error "livsRepair: Partial definition not in heap"
            let new_def = insertSubExpr partial_def (stripLeadingLams sub_def)

            -- Add the new definition to the heap
            let h'' = H.insertDef (idName (head is'')) new_def $ H.filterWithKey (\n' _ -> idName (head is'') /= n') h'
            let is''' = [Id (idName (head is'')) (typeOf original_def)]

            -- Check that new definition of the function works in the real langauge
            mapM_ (\i -> case H.lookup (idName i) h'' of
                            Just (H.Def e) -> do
                              def le b i e
                            _ -> error "livsRepair: No definition found") is'''
            incor <- incorrectSuspects le b $ map Suspect exs
            case incor of
                [] -> return ()
                _ -> error $ "livsSynth: Incorrect translation back to real language"

            -- Score the new definition against the original definition for difference
            let score = scoreExpr original_def new_def

            -- Debugging
            liftIO $ (putStr $ "Synthesized repair: " ++ toJavaScriptDef S.empty (idName (head is)) new_def)
            liftIO $ (putStrLn $ "Score: " ++ (show score) ++ "\n")

            -- Call repair recursively to get the best scores for repairing all of the subexpressions of the target function
            let at = mkTyFun (argTypes original_def)
            all_scores <- mapM (livsRepair' con le b gen cg sub h tenv exs exs' is original_def) (getSubExprs at original_def partial_def)

            -- Return the heap that scored the highest in similarity to the target function
            let all_scores' = all_scores ++ [(h'', is''', score)]
                high_score = maximum $ map (\(_, _, s) -> s) all_scores'
            return (head $ filter (\(_, _, s) -> s == high_score) all_scores')

callSynthesizer :: MonadIO m
                => LIVSConfigNames
                -> Gen m
                -> CallGraph
                -> Sub.SubFunctions
                -> H.Heap
                -> T.TypeEnv
                -> [Example]
                -> [Id]
                -> m (H.Heap, [Id])
callSynthesizer con gen cg sub h tenv exs is = do

    liftIO $ whenLoud (putStrLn $ "Synthesizing expression " ++ show (head is))

    -- Expand the call graph with the new Id
    let def_ids = filterNonPrimitives h $ verts cg
        cg' = addVertsToCallGraph (zip is $ repeat def_ids) cg

    -- The heap as seen from the function we're synthesizing
    let relH = H.filterWithKey (\n' _ -> idName (head is) /= n') $ filterToReachable con (head is) cg' h

    -- The grammar available to the function we're synthesizing
    let gram = S.fromList $ flip Sub.lookupAllNamesDefSingleton sub $ map idName $ directlyCalls (head is) cg'

    -- Take a guess at the definition of the function
    (m, sub') <- gen relH sub tenv gram exs
    case m of
        Sat m' -> do
            liftIO $ whenLoud (putStrLn $ "Synthesized expression " ++ show (head is))
            let h' = H.union (H.fromExprHashMap m') h
                is' = map (toId h') . flip Sub.lookupAllNames sub' $ map idName is
            return (h', is')

        _ -> do
            liftIO $ whenLoud (putStrLn $ "Failed synthesis for expression " ++ show (head is))
            return (h, [])

    where
        toId heap n
            | Just e <- H.lookup n heap = Id n (typeOf e)
            | otherwise = error "toId: Name not in Heap"

scoreExpr :: Expr -> Expr -> Int
scoreExpr (Lam i1 e1) (Lam i2 e2) = (scoreExpr e1 e2) + (scoreEq i1 i2)
scoreExpr (App e11 e12) (App e21 e22) = (scoreExpr e11 e21) + (scoreExpr e12 e22)
scoreExpr (Let b1 e1) (Let b2 e2) = (scoreExpr e1 e2) + (scoreEq (fst b1) (fst b2)) + (scoreExpr (snd b1) (snd b2))
scoreExpr (Var i1) (Var i2) = scoreEq i1 i2
scoreExpr (Data d1) (Data d2) = scoreEq d1 d2
scoreExpr (Lit l1) (Lit l2) = scoreEq l1 l2
scoreExpr _ _ = -1

scoreEq :: Eq a => a -> a -> Int
scoreEq a b = if (a == b) then 0 else -1

getSubExprs :: Type -> Expr -> Expr -> [(Expr, Type)]
getSubExprs t (Lam i e) EmptyExpr = [(Lam i EmptyExpr, TyFun t (typeOf e))]
getSubExprs t (App e1 e2) EmptyExpr = [(App e1 EmptyExpr, TyFun t (typeOf e2))] ++
                                      map (\(e, tp) -> (App e e2, tp)) (getSubExprs t e1 EmptyExpr)
getSubExprs t (Let b e) EmptyExpr = filterFuncCalls e (Let b EmptyExpr, TyFun t (typeOf e))
getSubExprs t (Lam i e1) (Lam _ e2) = map (\(e, tp) -> (Lam i e, tp)) (getSubExprs t e1 e2)
getSubExprs t (App e11 e12) (App e21 e22) = map (\(e, tp) -> (App e e12, tp)) (getSubExprs t e11 e21) ++
                                            map (\(e, tp) -> (App e11 e, tp)) (getSubExprs t e12 e22)
getSubExprs t (Let b1 e1) (Let b2 e2) = map (\(e, tp) -> (Let b1 e, tp)) (getSubExprs t e1 e2) ++
                                        map (\(e, tp) -> (Let (fst b1, e) e1, tp)) (getSubExprs t (snd b1) (snd b2))
getSubExprs _ _ _ = []

filterFuncCalls :: Expr -> (Expr, Type) -> [(Expr, Type)]
filterFuncCalls (Var (Id _ (TyFun _ _))) _ = []
filterFuncCalls _ e = [e]

insertSubExpr :: Expr -> Expr -> Expr
insertSubExpr EmptyExpr subExpr = subExpr
insertSubExpr (Lam i e) subExpr = Lam i (insertSubExpr e subExpr)
insertSubExpr (App e1 e2) subExpr = App (insertSubExpr e1 subExpr) (insertSubExpr e2 subExpr)
insertSubExpr (Let b e) subExpr = Let (fst b, insertSubExpr (snd b) subExpr) (insertSubExpr e subExpr)
insertSubExpr e _ = e
