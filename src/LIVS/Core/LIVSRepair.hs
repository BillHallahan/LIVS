-- | LIVS to repair functions.
-- Unlike the general LIVS algorithm, modifies existing functions and tries to
-- preserve their properties using fault localization via abstract interpretation
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
livsRepair con le b gen fuzz fp cg h tenv fstring exs = do

    -- Get the function to repair
    let v = verts cg
        ids = filter (\(Id (Name _ n _) _) -> n == fstring) v
        fid = case ids of
                  [] -> error "LivsRepair: Repair target does not exist"
                  _ -> head ids
        fname = idName fid

    -- Get the list of functions whose examples we will need for this repair
    let relevant_funcs = [fid] ++ filter (\i -> path cg i fid) v

    -- Get the relevant examples for this repair
    let exs' = filter (\Example{func = i} -> i `elem` relevant_funcs) exs
    let ext_exs = filter (\e -> (func e) /= fid) exs'
    _ <- case exs' of
             [] -> error "LivsRepair: No relevant examples for repair target"
             _ -> return ()

    -- Constraining functions (functions that we need the syntactic definitions of)
    -- are only those that the external example functions will actually call on the
    -- way to the target function (along with the target function itself)
    let constraining_funcs = [fid] ++ (nub $ concatMap (\Example{func = i} -> allPaths i fid cg) ext_exs)

    -- Pull definitions from the source code and into the intermediate language
    defs <- extractDefs le fp $ map idName constraining_funcs
    let ext_defs = HM.filterWithKey (\n _ -> n /= fname) defs
        target_def = head $ HM.elems $ HM.filterWithKey (\n _ -> n == fname) defs
    liftIO $ whenLoud (putStrLn $ "Original function: " ++ toJavaScriptDef S.empty fname target_def)

    -- TODO: should only need to map sygus vals onto partial defs, and unmap from final result
    -- Map the variables in the constraint expressions to their sygus counterparts
    -- so that the variable names in synthesized sub-expressions will match up
    -- let sygus_vars = map (flip Id TYPE) [Name Ident ("x" ++ show i ++ "_") Nothing | i <- [1..] :: [Integer]]
    --     sygus_var_mappings = HM.fromList $ map (\(i, e) -> (i, zip (leadingLams e) $ map Var sygus_vars)) (HM.toList all_defs)
    --     all_defs' = HM.fromList $ map (\(i, e) -> (i, mapVars e $ HM.fromList $ (case HM.lookup i sygus_var_mappings of
    --                                                                                  Just m -> m
    --                                                                                  _ -> error ""))) (HM.toList all_defs)

    -- Convert the relevant examples from external functions to constraints on the target function
    let ext_constraints = map (\ex -> extExampleToConstraint ex fid cg ext_defs) ext_exs

    -- Get all possible partial definitions to repair on
    let inpt_types = mkTyFun (argTypes target_def)
        otpt_type = returnType target_def
        call_expr = (makeCallExpr fid $ map Var (leadingLams target_def))
        partial_defs = map makeFuncAndType $ [(call_expr, otpt_type)] ++ getPartialDefs call_expr (stripLeadingLams target_def)
            where
                makeFuncAndType (e, t) = (mkLams (leadingLams target_def) e, TyFun inpt_types t)

    -- Get definitions for usable component functions
    let cg' = ( \g@(CallGraph _ _ _ ve) i -> createCallGraph [x | x <- ve, not $ path g (fst x) i] ) cg fid
    (h', sub, exs'') <- livs con le b gen fuzz fp cg' h tenv
    let exs''' = examplesForFunc fname (exs ++ exs'')

    -- Repair!
    all_scores <- mapM (livsRepair' con le b gen cg sub h' tenv exs exs''' ext_constraints fname target_def) partial_defs
    let high_score = maximum $ map (\(_, _, s) -> s) all_scores
        (h'', success, _) = (head $ filter (\(_, _, s) -> s == high_score) all_scores)
    let fid' = case success of
                   Nothing -> error "livsRepair: Repair failed"
                   Just i -> i

    -- Map the old variables back onto the function so that the returned function has it's original variable
    -- names and not the syugs variable names
    -- let fname' = idName fid'
    -- let reverse_mapping = HM.fromList $ map TP.swap $ (case HM.lookup fname sygus_var_mappings of
    --                                                        Just m -> m
    --                                                        _ -> error "livsRepair: Missing mapping")
    -- let new_def = case H.lookup fname' h'' of
    --                   Just (H.Def e) -> mapVars e reverse_mapping
    --                   _ -> error "livsRepair: No definition found"
    -- let h''' = H.insertDef fname' new_def (H.filterWithKey (\n' _ -> fname' /= n') h'')
    return (h'', [fid'])

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
            -> [Example]
            -> Name
            -> Expr
            -> (Expr, Type)
            -> m (H.Heap, Maybe Id, Int)
livsRepair' con le b gen cg sub h tenv exs exs' ext_constraints fname original_def (partial_def, t) = do

    -- Get I/O constraints and an id for the subexpression to synthesize
    let fid = Id fname t
    let int_constraints = map (\(Example _ it ot) -> Constraint fid it ot partial_def) exs'
    let ext_constraints' = map ( \c@(Constraint{expr = ext_def}) ->
                                  c{func = fid, expr = inline fname ext_def partial_def} ) ext_constraints
    let constraints = int_constraints ++ ext_constraints'

    liftIO $ (putStr $ "Repair area: " ++ toJavaScriptDef S.empty fname partial_def)
    --liftIO $ print partial_def

    -- Synthesize sub expression
    (h', success) <- callSynthesizer con gen cg sub h tenv constraints fid
    case success of
        Nothing -> do
            liftIO $ (putStrLn "Synthesis failed for this repair area\n")
            return (h', Nothing, -1000)
        Just fid' -> do

            -- Insert the synthesized subexpression into our partial definition
            -- to create a full version of the target function
            let fname' = idName fid'
            let sub_def = case H.lookup fname' h' of
                             Just (H.Def e) -> e
                             _ -> error "livsRepair: Partial definition not in heap"
            let new_def = inline fname partial_def sub_def

            -- Add the new definition to the heap
            let h'' = H.insertDef fname' new_def $ H.filterWithKey (\n' _ -> fname' /= n') h'
            let fid'' = Id fname' (typeOf original_def)
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
            liftIO $ (putStrLn $ "Score: " ++ (show score) ++ "\n")

            -- Return the heap with it's score
            return (h'', Just fid'', score)

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

extExampleToConstraint :: Example -> Id -> CallGraph -> HM.HashMap Name Expr -> Example
extExampleToConstraint (Example i inpts otpts) fid cg defs =
    let
        e = case HM.lookup (idName i) defs of
                Just e' -> e'
                _ -> error "Missing definition"
    in
    Constraint i inpts otpts (expandConstraintExpr i e fid cg defs)

expandConstraintExpr :: Id -> Expr -> Id -> CallGraph -> HM.HashMap Name Expr -> Expr
expandConstraintExpr i e fid cg defs =
    let
        expandable_ids = cycle $ allPaths i fid cg
        inlineFromHash = (\e' i' -> inline (idName i') e' (case HM.lookup (idName i') defs of
                                                               Just e'' -> e''
                                                               _ -> error "Missing definition"))
    in
    scanl inlineFromHash e expandable_ids !! 50 --TODO: want more intelligent way to decide we're done expanding

inline :: Name -> Expr -> Expr -> Expr
inline n (App v@(Var (Id n2 _)) e2) subExpr = if (n == n2)
                                            then mapVars (stripLeadingLams subExpr) (HM.fromList $ zip (leadingLams subExpr) (unApp e2))
                                            else App v (inline n e2 subExpr)
inline n (Lam is e) subExpr = Lam is (inline n e subExpr)
inline n (Let b e) subExpr = Let (fst b, inline n (snd b) subExpr) (inline n e subExpr)
inline n (App e1 e2) subExpr = App (inline n e1 subExpr) (inline n e2 subExpr)
inline _ e _ = e

mapVars :: Expr -> HM.HashMap Id Expr -> Expr
mapVars (Var i) hm = case (HM.lookup i hm) of
                                Just new_i -> new_i
                                _ -> Var i
mapVars (Lam i e) hm = case (HM.lookup i hm) of
                                Just _ -> error "Unexpected Lam"
                                _ -> Lam i (mapVars e hm)
mapVars (App e1 e2) hm = App (mapVars e1 hm) (mapVars e2 hm)
mapVars (Let (b, e1) e2) hm = Let (b, mapVars e1 hm) (mapVars e2 hm)
mapVars e _ = e

getPartialDefs :: Expr -> Expr -> [(Expr, Type)]
getPartialDefs c (Let b e) = [(Let b c, typeOf e)] ++ (map (\(e', tp) -> (Let b e', tp)) $ getPartialDefs c e)
getPartialDefs c (Lam i e) = [(Lam i c, typeOf e)] ++ (map (\(e', tp) -> (Lam i e', tp)) $ getPartialDefs c e)
getPartialDefs c (App e1 e2) = [(App e1 c, typeOf e2)] ++ (map (\(e', tp) -> (App e1 e', tp)) $ getPartialDefs c e2) ++
                                                          (map (\(e', tp) -> (App e' e2, tp)) $ getPartialDefs c e1)
getPartialDefs _ _ = []

makeCallExpr :: Id -> [Expr] -> Expr
makeCallExpr i args = mkApp $ [Var i] ++ args

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
