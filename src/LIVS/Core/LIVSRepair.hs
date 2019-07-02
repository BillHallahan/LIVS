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
import Data.List
import Data.Maybe

-- CORE

livsRepairCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m) => LIVSConfigNames -> LanguageEnv m b -> b -> Fuzz m b
               -> FilePath -> CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> String -> [Example] -> m (H.Heap, [Id])
livsRepairCVC4 con le b fuzz fp cg const_val = livsRepair con le b (runSygusWithGrammar con cg const_val) fuzz fp cg

livsRepair :: MonadIO m => LIVSConfigNames -> LanguageEnv m b -> b -> Gen m -> Fuzz m b -> FilePath
           -> CallGraph -> H.Heap -> T.TypeEnv -> String -> [Example] -> m (H.Heap, [Id])
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

    -- Convert the relevant examples from external functions to constraints on the target function
    let ext_constraints = map (\ex -> extExampleToConstraint ex fid cg ext_defs) ext_exs

    -- Get all possible partial definitions to repair on
    let call_expr = (makeCallExpr fid $ map Var (leadingLams target_def))
        partial_defs = getPartialDefs call_expr (stripLeadingLams target_def)

    -- Get definitions for usable component functions
    let cg' = (\g@(CallGraph _ _ _ ve) i -> createCallGraph [x | x <- ve, (fst x /= i) && (not $ path g (fst x) i)]) cg fid
    (h', sub, exs'') <- livs con le b gen fuzz fp cg' h tenv
    let exs''' = examplesForFunc fname (exs ++ exs'')

    -- Repair!
    (h'', success, _) <- livsRepair' le b gen cg sub h' tenv exs exs''' ext_constraints fname target_def partial_defs
    let fid' = case success of
                   Nothing -> error "livsRepair: Repair failed"
                   Just i -> i
    return (h'', [fid'])

livsRepair' :: MonadIO m => LanguageEnv m b -> b -> Gen m -> CallGraph -> Sub.SubFunctions -> H.Heap -> T.TypeEnv
            -> [Example] -> [Example] -> [Example] -> Name -> Expr -> DefT -> m (H.Heap, Maybe Id, Int)
livsRepair' le b gen cg sub h tenv exs exs' ext_cons fname target_def (DefT partial_def children) = do

    -- Give the partial definition the input types of the target definition
    let e = mkLams (leadingLams target_def) (fst partial_def)
        e_type = mkTyFun $ [snd partial_def] ++ argTypes target_def
        partial_def' = (e, e_type)

    --liftIO $ (putStrLn $ "Partial Def: " ++ show partial_def')

    -- Attempt repair at current location
    (h', fid, score) <- livsRepairStep le b gen cg sub h tenv exs exs' ext_cons fname target_def partial_def'
    case fid of
        Nothing -> do
            return (h', Nothing, score)
        Just _ -> do

            -- If the repair succeeded, try repair on child subexpressions too
            all_scores <- mapM (livsRepair' le b gen cg sub h' tenv exs exs' ext_cons fname target_def) children
            let all_scores' = [(h', fid, score)] ++ filter (\(_, f, _) -> isJust f) all_scores

            -- Get the lowest scoring (best) repair and return it
            let best_score = minimum $ map (\(_, _, s) -> s) all_scores'
                (best_h, best_fid, _) = (head $ filter (\(_, _, s) -> s == best_score) all_scores')
            return (best_h, best_fid, best_score)

livsRepairStep :: MonadIO m => LanguageEnv m b -> b -> Gen m -> CallGraph -> Sub.SubFunctions -> H.Heap -> T.TypeEnv
               -> [Example] -> [Example] -> [Example] -> Name -> Expr -> PartialDef -> m (H.Heap, Maybe Id, Int)
livsRepairStep le b gen cg sub h tenv exs exs' ext_constraints fname original_def (partial_def, t) = do

    -- Get I/O constraints and an id for the subexpression to synthesize
    let fid = Id fname t
    let int_constraints = map (\(Example _ it ot) -> Constraint fid it ot partial_def) exs'
    let ext_constraints' = map ( \c@(Constraint{expr = ext_def}) ->
                                  c{func = fid, expr = inline fname ext_def partial_def} ) ext_constraints
    let constraints = int_constraints ++ ext_constraints'

    liftIO $ whenLoud (putStr $ "Repair area: " ++ toJavaScriptDef S.empty fname partial_def)

    -- Synthesize sub expression
    (h', success) <- callSynthesizer gen cg sub h tenv constraints fid
    case success of
        Nothing -> do
            liftIO $ whenLoud (putStrLn "Synthesis failed for this repair area\n")
            return (h', Nothing, 0)
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
            liftIO $ whenLoud (putStr $ "Synthesized repair: " ++ toJavaScriptDef S.empty fname' new_def)

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
            liftIO $ whenLoud (putStrLn $ "Score: " ++ (show score) ++ "\n")

            -- Return the heap with it's score
            return (h'', Just fid'', score)

callSynthesizer :: MonadIO m => Gen m -> CallGraph -> Sub.SubFunctions -> H.Heap
                -> T.TypeEnv -> [Example] -> Id -> m (H.Heap, Maybe Id)
callSynthesizer gen cg sub h tenv exs fid = do

    -- The grammar available to the function we're synthesizing
    let def_ids = nub $ filterNonPrimitives h $ verts cg
        gram = S.fromList $ flip Sub.lookupAllNamesDefSingleton sub $ map idName def_ids
    liftIO $ whenLoud (putStrLn $ "Grammar: " ++ (show gram))

    -- Take a guess at the definition of the function
    (m, sub') <- gen h sub tenv gram exs
    case m of
        Sat m' -> do
            let h' = H.union (H.fromExprHashMap m') h
                fid' = head $ map (toId h') $ Sub.lookupAllNames [idName fid] sub'
            return (h', Just fid')
        _ -> return (h, Nothing)

    where
        toId heap n
            | Just e <- H.lookup n heap = Id n (typeOf e)
            | otherwise = error "toId: Name not in Heap"

-- CONSTRAINT ACCUMULATION

extExampleToConstraint :: Example -> Id -> CallGraph -> HM.HashMap Name Expr -> Example
extExampleToConstraint (Example i inpts otpts) fid cg defs =
    let
        e = case HM.lookup (idName i) defs of
                Just e' -> e'
                _ -> error "Missing definition"
    in
    Constraint i inpts otpts (expandConstraintExpr i e fid cg defs)
extExampleToConstraint _ _ _ _ = error "Only examples can be converted to constraints"

expandConstraintExpr :: Id -> Expr -> Id -> CallGraph -> HM.HashMap Name Expr -> Expr
expandConstraintExpr i e fid cg defs =
    let
        expandable_ids = cycle $ delete fid (allPaths i fid cg)
        inlineFromHash = (\e' i' -> inline (idName i') e' (case HM.lookup (idName i') defs of
                                                               Just e'' -> e''
                                                               _ -> error $ "Missing definition: " ++ show (idName i')))
    in
    scanl inlineFromHash e expandable_ids !! 50 --TODO: want more intelligent way to decide we're done expanding

inline :: Name -> Expr -> Expr -> Expr
inline n (Lam is e) subExpr = Lam is (inline n e subExpr)
inline n (Let b e) subExpr = Let (fst b, inline n (snd b) subExpr) (inline n e subExpr)
inline n e@(App e1 e2) subExpr
    | isCallExpr n e = mapVars (stripLeadingLams subExpr) (HM.fromList $ zip (leadingLams subExpr) (appArgs e))
    | otherwise = App (inline n e1 subExpr) (inline n e2 subExpr)
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

-- PARTIAL DEFINITIONS

type PartialDef = (Expr, Type)
data DefT = DefT PartialDef [DefT] deriving (Eq, Show, Read)

getPartialDefs :: Expr -> Expr -> DefT
getPartialDefs c d = DefT (c, typeOf d) (getPartialDefs' c d)

getPartialDefs' :: Expr -> Expr -> [DefT]
getPartialDefs' c (Lam i e) = [mapDefT (Lam i) $ getPartialDefs c e]
getPartialDefs' c (Let (i, e1) e2) = [mapDefT (\e' -> Let (i, e') e2) $ getPartialDefs c e1,
                                      mapDefT (Let (i, e1)) $ getPartialDefs c e2]
getPartialDefs' c (App e1 e2) = [mapDefT (App e1) $ getPartialDefs c e2] ++
                                map (mapDefT $ flip App e2) (getPartialDefs' c e1)
getPartialDefs' _ _ = []

mapDefT :: (Expr -> Expr) -> DefT -> DefT
mapDefT f (DefT (e, t) l) = DefT (f e, t) (map (mapDefT f) l)

-- AST SCORING

type ForestKey = (Maybe (Int, Int), Maybe (Int, Int))
type ForestMap = HM.HashMap ForestKey Int
type DistanceTable = [[Int]]

scoreExpr :: Expr -> Expr -> Int
scoreExpr e1 e2 =
    let
        forest1 = postOrderLabel e1
        forest2 = postOrderLabel e2

        l1 = getLeftLeaf forest1
        l2 = getLeftLeaf forest2

        lr_keyroots1 = getKeyroots forest1 l1
        lr_keyroots2 = getKeyroots forest2 l2

        distTable = replicate (exprSize e1) $ replicate (exprSize e2) (-1)

        computeRow tbl i = foldl (flip $ treeDistance forest1 forest2 l1 l2 i) tbl lr_keyroots2
        computeTable tbl = foldl computeRow tbl lr_keyroots1
    in
    last . last $ computeTable distTable

exprSize :: Expr -> Int
exprSize (Lam _ e') = 1 + exprSize e'
exprSize (App e' e'') = 1 + exprSize e' + exprSize e''
exprSize (Let (_, e') e'') = 1 + exprSize e' + exprSize e''
exprSize _ = 1

postOrderLabel :: Expr -> [Expr]
postOrderLabel e@(Lam _ e') = postOrderLabel e' ++ [e]
postOrderLabel e@(App e' e'') = postOrderLabel e' ++ postOrderLabel e'' ++ [e]
postOrderLabel e@(Let (_, e') e'') = postOrderLabel e' ++ postOrderLabel e'' ++ [e]
postOrderLabel e = [e]

getLeftLeaf :: [Expr] -> Int -> Int
getLeftLeaf f i = i - (exprSize $ f !! i) + 1

getKeyroots :: [Expr] -> (Int -> Int) -> [Int]
getKeyroots forest l =
    let
        end = (length forest) - 1
    in
    filter (\k -> all (\k' -> l k /= l k') [(k + 1)..end]) [0..end]

treeDistance :: [Expr] -> [Expr] -> (Int -> Int) -> (Int -> Int) -> Int -> Int -> DistanceTable -> DistanceTable
treeDistance f1 f2 l1 l2 i j distTable =
    let
        forestDist = HM.singleton (Nothing :: Maybe (Int, Int), Nothing :: Maybe (Int, Int)) (0 :: Int)

        li = l1 i
        ikeys = [li..i]
        nothingColumn hm i' = forestDistSet hm (makeKey li i' 0 (-1)) (prev + cost)
            where
                prev = forestDistGet hm (makeKey li (i'-1) 0 (-1))
                cost = editCost f1 f2 (Just i') Nothing
        forestDist' = foldl nothingColumn forestDist ikeys

        lj = l2 j
        jkeys = [lj..j]
        nothingRow hm j' = forestDistSet hm (makeKey 0 (-1) lj j') (prev + cost)
            where
                prev = forestDistGet hm (makeKey 0 (-1) lj (j'-1))
                cost = editCost f1 f2 Nothing (Just j')
        forestDist'' = foldl nothingRow forestDist' jkeys

        fInsert = forestInsert f1 f2 l1 l2 li lj
        computeRow (tbl, hm) i' = foldl (\(tbl', hm') j' -> fInsert i' j' hm' tbl') (tbl, hm) jkeys
        computeTable hm = fst $ foldl computeRow (distTable, hm) ikeys
    in
    computeTable forestDist''

forestInsert :: [Expr] -> [Expr] -> (Int -> Int) -> (Int -> Int) -> Int -> Int
             -> Int -> Int -> ForestMap -> DistanceTable -> (DistanceTable, ForestMap)
forestInsert f1 f2 l1 l2 li lj i' j' hm distTable
    | (li == l1 i') && (lj == l2 j') = (treeDistSet distTable i' j' tree_val, forestDistSet hm key tree_val)
    | otherwise = (distTable, forestDistSet hm key forest_val)
    where
        deleteCost = forestDistGet hm (makeKey li (i' - 1) lj j') + editCost f1 f2 (Just i') Nothing
        insertCost = forestDistGet hm (makeKey li i' lj (j' - 1)) + editCost f1 f2 Nothing (Just j')
        swapCost = forestDistGet hm (makeKey li (i' - 1) lj (j' - 1)) + editCost f1 f2 (Just i') (Just j')
        distCost = forestDistGet hm (makeKey li (i' - 1) lj (j' - 1)) + case treeDistGet distTable i' j' of
                                                                             (-1) -> error $ "bad distance table lookup"
                                                                             val -> val
        tree_val = minimum [deleteCost, insertCost, swapCost]
        forest_val = minimum [deleteCost, insertCost, distCost]
        key = makeKey li i' lj j'

makeKey :: Int -> Int -> Int -> Int -> ForestKey
makeKey i i' j j' = validKey (Just (i, i'), Just (j, j'))

validKey :: ForestKey -> ForestKey
validKey (ibounds, jbounds) = (checkOrdered ibounds, checkOrdered jbounds)

checkOrdered :: Maybe (Int, Int) -> Maybe (Int, Int)
checkOrdered k@(Just (lo, hi)) = if lo <= hi then k else Nothing
checkOrdered _ = Nothing

forestDistGet :: ForestMap -> ForestKey -> Int
forestDistGet hm k = case HM.lookup k hm of
                         Just val -> val
                         _ -> error $ "Bad forest mapping: " ++ show k

forestDistSet :: ForestMap -> ForestKey -> Int -> ForestMap
forestDistSet hm k val = if val < 0
                         then error "negative forest distance"
                         else HM.insert k val hm

treeDistGet :: DistanceTable -> Int -> Int -> Int
treeDistGet tbl i j = (tbl !! i) !! j

treeDistSet :: DistanceTable -> Int -> Int -> Int -> DistanceTable
treeDistSet tbl i j val =
    let
        listSet lst i' val' = take i' lst ++ val' : drop (i' + 1) lst
    in
    if val < 0
    then error "negative tree distance"
    else listSet tbl i (listSet (tbl !! i) j val)

editCost :: [Expr] -> [Expr] -> Maybe Int -> Maybe Int -> Int
editCost f1 f2 (Just i) (Just j) = editCost' (Just (f1 !! i)) (Just (f2 !! j))
editCost _ f2 Nothing (Just j) = editCost' Nothing (Just (f2 !! j))
editCost f1 _ (Just i) Nothing = editCost' (Just (f1 !! i)) Nothing
editCost _ _ _ _ = error "Bad edit operation"

editCost' :: Maybe Expr -> Maybe Expr -> Int
editCost' Nothing _ = 1
editCost' _ Nothing = 1
editCost' (Just (Var (Id n _))) (Just (Var (Id n' _))) = eqCost n n'
editCost' (Just (Data dc)) (Just (Data dc')) = eqCost dc dc'
editCost' (Just (Lit l)) (Just (Lit l')) = eqCost l l'
editCost' (Just (Let (i, _) _)) (Just (Let (i', _) _)) = eqCost i i'
editCost' (Just (Lam (Id n _) _)) (Just (Lam (Id n' _) _)) = eqCost n n'
editCost' (Just (App _ _)) (Just (App _ _)) = 0
editCost' _ _ = 1

eqCost :: Eq a => a -> a -> Int
eqCost a b = if (a == b) then 0 else 1
