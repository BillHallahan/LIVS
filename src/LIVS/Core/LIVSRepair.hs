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
import qualified Data.HashMap.Lazy as HM
import qualified Data.Tuple as TP
import Data.List

livsRepairCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m)
               => LIVSConfigNames
               -> LanguageEnv m b
               -> b
               -> Fuzz m b
               -> FilePath
               -> CallGraph
               -> [Val]
               -> H.Heap
               -> T.TypeEnv
               -> String
               -> [Example]
               -> m (H.Heap, [Id])
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
           -> String
           -> [Example]
           -> m (H.Heap, [Id])
livsRepair con le b gen fuzz fp cg h tenv target exs = do

    -- Get the Id of the function to repair
    let ids = filter (\(Id (Name _ n _) _) -> n == target) (verts cg)
        fid = case ids of
                  [] -> error "LivsRepair: Repair target does not exist"
                  _ -> head ids
        fname = idName fid

    -- Get the relevant examples
    let exs' = filter (\Example{func = i} -> i == fid) exs
    _ <- case exs' of
             [] -> error "LivsRepair: No relevant examples for repair target"
             _ -> return ()

    -- Modify call graph so that it only includes the functions
    -- for which there is no path to the target function
    let cg' = ( \g@(CallGraph _ _ _ ve) i -> createCallGraph [x | x <- ve, not $ path g (fst x) i] ) cg fid

    -- Get definitions for usable component functions
    (h', sub, exs'') <- livs con le b gen fuzz fp cg' h tenv
    let exs''' = examplesForFunc fname (exs' ++ exs'')

    -- Convert the source code for the target function into an Expr
    original_def <- extractDef le fp fname
    liftIO $ whenLoud (putStrLn $ "Original function: " ++ toJavaScriptDef S.empty fname original_def)

    -- Map the variables in the target function to their sygus counterparts so that the variable
    -- names in synthesized sub-expressions will match up
    let sygus_vars = [Name Ident ("x" ++ show i ++ "_") Nothing | i <- [1..] :: [Integer]]
        sygus_var_mapping = zip (map idName $ leadingLams original_def) sygus_vars
        original_def' = mapVars original_def (HM.fromList sygus_var_mapping)

    -- Start repairing at the highest level (synthesized subexpression is the entire function)
    let partial_def = mkLams (leadingLams original_def') EmptyExpr
        partial_def' = (partial_def, (idType fid))
    (h'', success, _) <- livsRepair' con le b gen cg' sub h' tenv exs' exs''' fname original_def' partial_def'
    let fid' = case success of
                   Nothing -> error "livsRepair: Repair failed"
                   Just i -> i

    -- Map the old variables back onto the function so that the returned function has it's original variable
    -- names and not the syugs variable names
    let fname' = idName fid'
    let reverse_mapping = HM.fromList $ map TP.swap sygus_var_mapping
        new_def = case H.lookup fname' h'' of
                      Just (H.Def e) -> mapVars e reverse_mapping
                      _ -> error "livsRepair: No definition found"
    let h''' = H.insertDef fname' new_def (H.filterWithKey (\n' _ -> fname' /= n') h'')
    return (h''', [fid'])

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
            -> Name
            -> Expr
            -> (Expr, Type)
            -> m (H.Heap, Maybe Id, Int)
livsRepair' con le b gen cg sub h tenv exs exs' fname original_def (partial_def, t) = do

    -- Get I/O constraints and an id for the sub expression to synthesize
    let constraints = map (\(Example i it ot) -> Constraint i it ot partial_def) exs'
    let fid = Id fname t

    -- Debugging
    liftIO $ (putStr $ "Repair area: " ++ toJavaScriptDef S.empty fname partial_def)

    -- Synthesize sub expression
    (h', success) <- callSynthesizer con gen cg sub h tenv constraints fid
    case success of
        Nothing -> do
            liftIO $ (putStrLn "Synthesis failed for this repair area")
            return (h', Nothing, -1000)
        Just fid' -> do

            -- Insert the synthesized subexpression into our partial definition
            -- to create a full version of the target function
            let fname' = idName fid'
            let sub_def = case H.lookup fname' h' of
                             Just (H.Def e) -> e
                             _ -> error "livsRepair: Partial definition not in heap"
            let new_def = insertSubExpr partial_def (stripLeadingLams sub_def)

            -- Add the new definition to the heap
            let h'' = H.insertDef fname' new_def $ H.filterWithKey (\n' _ -> fname' /= n') h'
            let fid'' = Id fname' (typeOf original_def)

            -- Debugging
            liftIO $ (putStr $ "Synthesized repair: " ++ toJavaScriptDef S.empty fname' new_def)

            -- Check that new definition of the function works in the real langauge
            _ <- case H.lookup fname' h'' of
                     Just (H.Def e) -> do
                         def le b fid'' e
                     _ -> error "livsRepair: No definition found"
            incor <- incorrectSuspects le b $ map Suspect exs
            case incor of
                [] -> return ()
                _ -> error $ "livsSynth: Incorrect translation back to real language"

            -- Score the new definition against the original definition for difference
            let score = scoreExpr original_def new_def

            -- Debugging
            liftIO $ (putStrLn $ "Score: " ++ (show score) ++ "\n")

            -- Call repair recursively to get the best of all possible repairs
            let at = mkTyFun (argTypes original_def)
                sub_exprs = (getSubExprs at original_def partial_def)
            all_scores <- mapM (livsRepair' con le b gen cg sub h tenv exs exs' fname original_def) sub_exprs

            -- Return the heap that scored the highest in similarity to the target function
            let all_scores' = all_scores ++ [(h'', Just fid'', score)]
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
                -> Id
                -> m (H.Heap, Maybe Id)
callSynthesizer con gen cg sub h tenv exs fid = do

    liftIO $ whenLoud (putStrLn $ "Synthesizing expression " ++ show fid)

    -- Expand the call graph with the new Id
    let def_ids = filterNonPrimitives h $ verts cg
        cg' = addVertsToCallGraph (zip [fid] $ repeat def_ids) cg

    -- The heap as seen from the function we're synthesizing
    let fname = idName fid
    let relH = H.filterWithKey (\n' _ -> fname /= n') $ filterToReachable con fid cg' h

    -- The grammar available to the function we're synthesizing
    let gram = S.fromList $ flip Sub.lookupAllNamesDefSingleton sub $ map idName $ directlyCalls fid cg'

    -- Take a guess at the definition of the function
    (m, sub') <- gen relH sub tenv gram exs
    case m of
        Sat m' -> do
            let h' = H.union (H.fromExprHashMap m') h
                fid' = head $ map (toId h') $ Sub.lookupAllNames [fname] sub'
            return (h', Just fid')
        _ -> return (h, Nothing)

    where
        toId heap n
            | Just e <- H.lookup n heap = Id n (typeOf e)
            | otherwise = error "toId: Name not in Heap"

mapVars :: Expr -> HM.HashMap Name Name -> Expr
mapVars (Var (Id n t)) hm = case (HM.lookup n hm) of
                                Just new_n -> Var (Id new_n t)
                                _ -> Var (Id n t)
mapVars (Lam (Id n t) e) hm = case (HM.lookup n hm) of
                                Just new_n -> Lam (Id new_n t) (mapVars e hm)
                                _ -> Lam (Id n t) (mapVars e hm)
mapVars (App e1 e2) hm = App (mapVars e1 hm) (mapVars e2 hm)
mapVars (Let (b, e1) e2) hm = Let (b, mapVars e1 hm) (mapVars e2 hm)
mapVars e _ = e

scoreExpr :: Expr -> Expr -> Int
scoreExpr (Lam (Id n1 _) e1) (Lam (Id n2 _) e2) = (scoreExpr e1 e2) + (scoreEq n1 n2)
scoreExpr (App e11 e12) (App e21 e22) = (scoreExpr e11 e21) + (scoreExpr e12 e22)
scoreExpr (Let b1 e1) (Let b2 e2) = (scoreExpr e1 e2) + (scoreExpr (snd b1) (snd b2))
scoreExpr (Var (Id n1 _)) (Var (Id n2 _)) = scoreEq n1 n2
scoreExpr (Data d1) (Data d2) = scoreEq d1 d2
scoreExpr (Lit l1) (Lit l2) = scoreEq l1 l2
scoreExpr _ _ = -1

scoreEq :: Eq a => a -> a -> Int
scoreEq a b = if (a == b) then 0 else -1

getSubExprs :: Type -> Expr -> Expr -> [(Expr, Type)]
getSubExprs t (Lam i e) EmptyExpr = [(Lam i EmptyExpr, TyFun t (typeOf e))]
getSubExprs t (App e1 e2) EmptyExpr = [(App e1 EmptyExpr, TyFun t (typeOf e2))] ++
                                      map (\(e, tp) -> (App e e2, tp)) (getSubExprs t e1 EmptyExpr)
getSubExprs t (Let b e) EmptyExpr = [(Let b EmptyExpr, TyFun t (typeOf e))]
getSubExprs t (Lam i e1) (Lam _ e2) = map (\(e, tp) -> (Lam i e, tp)) (getSubExprs t e1 e2)
getSubExprs t (App e11 e12) (App e21 e22) = map (\(e, tp) -> (App e e12, tp)) (getSubExprs t e11 e21) ++
                                            map (\(e, tp) -> (App e11 e, tp)) (getSubExprs t e12 e22)
getSubExprs t (Let b1 e1) (Let b2 e2) = map (\(e, tp) -> (Let b1 e, tp)) (getSubExprs t e1 e2) ++
                                        map (\(e, tp) -> (Let (fst b1, e) e1, tp)) (getSubExprs t (snd b1) (snd b2))
getSubExprs _ _ _ = []

insertSubExpr :: Expr -> Expr -> Expr
insertSubExpr EmptyExpr subExpr = subExpr
insertSubExpr (Lam i e) subExpr = Lam i (insertSubExpr e subExpr)
insertSubExpr (App e1 e2) subExpr = App (insertSubExpr e1 subExpr) (insertSubExpr e2 subExpr)
insertSubExpr (Let b e) subExpr = Let (fst b, insertSubExpr (snd b) subExpr) (insertSubExpr e subExpr)
insertSubExpr e _ = e
