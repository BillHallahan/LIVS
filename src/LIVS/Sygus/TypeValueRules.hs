-- should we call this ExampleGrouping or something instead?
module LIVS.Sygus.TypeValueRules ( typeValueRules
                                 , filterNotTypeValueRuleCovered

                                 , typeTypeRules
                                 , inputTypeRules
                                 , simplifyExamples
                                 , reassignFuncNames
                                 , reassignConstraintNames

                                 , generateTypeValueRulesFuncs
                                 , generateTypeValueRulesFunc
                                 , generateInputTypeRulesFunc ) where

import LIVS.Language.Expr
import LIVS.Language.Monad.Naming
import LIVS.Language.Syntax
import qualified LIVS.Language.SubFunctions as Sub
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Sygus.SMTPrims

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.List

import Control.Applicative
import Control.Monad.State.Lazy

-- | Establish rules about which input types that always lead to the same value
--   Identifies which input types generate an error value (or any fixed value)
typeValueRules :: [Example] -> [([DC],Val)]
typeValueRules es = let
    rs = map buildTypeValueRule es
  in
    filterRules' rs

filterRules' :: Eq a => [([DC], a)] -> [([DC], a)]
filterRules' rs = filterRules S.empty HM.empty rs

filterRules :: Eq a => S.HashSet [DC] -> HM.HashMap [DC] a -> [([DC],a)] -> [([DC],a)]
filterRules reject provisionalKeep ((dc,v):rs) =
    if S.member dc reject || (HM.lookupDefault v dc provisionalKeep /= v)
    then filterRules (S.insert dc reject) (HM.delete dc provisionalKeep) rs
    else filterRules reject (HM.insert dc v provisionalKeep) rs
filterRules _ provisionalKeep [] = HM.toList provisionalKeep

buildTypeValueRule :: Example -> ([DC],Val)
buildTypeValueRule e =
    (map valToDC $ input e, output e)

buildInputTypeRule :: Example -> ([DC], DC)
buildInputTypeRule e =
    (map valToDC $ input e, valToDC $ output e)

valToDC :: Val -> DC
valToDC v = case (appValCenter v) of
    DataVal dc -> dc
    LitVal l -> error $ "Bad call: had LitVal"++(show l)
    AppVal _ _-> error "Bad call: had AppVal"

-- | From a list of examples, removes all those already covered by one of the rules
filterNotTypeValueRuleCovered :: [([DC],Val)] -> [Example] -> [Example]
filterNotTypeValueRuleCovered dcv = filter (flip notElem dcv . buildTypeValueRule)

-- | Split a list of exmaples into lists of examples of matching types
--  :: [Example] -> [[Example]]

-- |
inputTypeRules :: [Example] -> [([DC], Maybe DC)]
inputTypeRules exs = let
    ttRules = HM.map Just $ HM.fromList $ typeTypeRules exs
    rs = HM.fromList $ map ((\(dcs,_) -> (dcs,Nothing)). buildTypeValueRule) exs
  in
    HM.toList $ HM.unionWith (<|>) rs ttRules


-- | Establish rules about which input types always lead to the same output type
typeTypeRules :: [Example] -> [([DC], DC)]
typeTypeRules es = let
    rs = map buildInputTypeRule es
  in
    filterRules' rs

-- | Takes a list of examples, and splits them up by the input data constructors.
-- Eliminates the data constructors from the input, and, (when possible) the output,
-- and returns a mapping from input/output data constructors to examples
simplifyExamples :: [Example] -> [(([DC], Maybe DC), [Example])]
simplifyExamples es =
    let
        r = inputTypeRules es
    in
    simplifyExamples' r es

-- | Removes the data constructors from the input and (when possible) output
simplifyExamples' :: [([DC], Maybe DC)] -> [Example] -> [(([DC], Maybe DC), [Example])]
simplifyExamples' dcs es = simplifyExamples'' $ groupInputTypeRules dcs es

simplifyExamples'' :: [(([DC], Maybe DC), [Example])] -> [(([DC], Maybe DC), [Example])]
simplifyExamples'' = map simplifyExample

simplifyExample :: (([DC], Maybe DC), [Example]) -> (([DC], Maybe DC), [Example])
simplifyExample ((dcs, mdc), es) = ((dcs, mdc), map simplifyExample' es)
  where
    simplifyExample' e =
        let
          is = tail $ exampleVals e
          out = head $ exampleVals e
          is' = map (\(i, dc) -> case i of
                                  AppVal (DataVal dc') v
                                    | dc' == dc -> v
                                    | otherwise -> i
                                  _ -> i) $ zip is dcs

          out' = case out of
                  AppVal (DataVal outDC) v
                    | Just outDC == mdc -> v
                    | otherwise -> out
                  _ -> out
        in
        e { input = is', output = out' }

-- | Group examples that share the same input data constructors together
groupInputTypeRules :: [([DC], a)] -> [Example] -> [(([DC], a), [Example])]
groupInputTypeRules dcvs es = map (\dcv -> (dcv, filterInputTypeRule dcv es)) dcvs

filterInputTypeRule :: ([DC], a) -> [Example] -> [Example]
filterInputTypeRule (dc, _) = filter ((==) dc . fst . buildInputTypeRule)

reassignFuncNames :: NameGenMonad m => Sub.SubFunctions -> Name -> [(([DC], Maybe DC), [Example])] -> m ([(([DC], Maybe DC), [Example])], Sub.SubFunctions)
reassignFuncNames sub orig_n es = do
  (es', sub') <- runStateT (mapM assignFuncName es) sub
  return (es', sub')
  where
    assignFuncName :: NameGenMonad m => (([DC], Maybe DC), [Example]) -> StateT Sub.SubFunctions m (([DC], Maybe DC), [Example])
    assignFuncName ((dcmdc, ess@(e:_))) = do
      let t = exampleFuncType e
      nsub <- get
      i <- case Sub.lookupName orig_n t nsub of
                    Just n -> return (Id n t)
                    Nothing -> do
                        i@(Id new_n _) <- freshIdM (idName $ func e) t
                        put $ Sub.insert orig_n t new_n nsub
                        return i
      return (dcmdc, map (\e' -> e' { func = i }) ess)
    assignFuncName _ = error "assignFuncNames: empty example list."

reassignConstraintNames :: Expr -> Sub.SubFunctions -> Expr
reassignConstraintNames d@(Data _) _ = d
reassignConstraintNames l@(Lit _) _ = l
reassignConstraintNames (App e1 e2) sub = App (reassignConstraintNames e1 sub) (reassignConstraintNames e2 sub)
reassignConstraintNames (Var i) sub = Var (substituteSMTName i sub)
reassignConstraintNames (Lam i e) sub = Lam (substituteSMTName i sub) (reassignConstraintNames e sub)
reassignConstraintNames (Let (i, e1) e2) sub = Let (substituteSMTName i sub, reassignConstraintNames e1 sub) (reassignConstraintNames e2 sub)

substituteSMTName :: Id -> Sub.SubFunctions -> Id
substituteSMTName (Id n t) sub = case Sub.lookupMaybe n sub of
                                    Just hm -> case length $ HM.elems hm of
                                                  1 -> (Id (head $ HM.elems hm) t)
                                                  _ -> error $ "Multiple SMT functions: " ++ show n ++ ": " ++ show hm
                                    Nothing -> (Id n t)

generateTypeValueRulesFuncs :: [([DC], Val)] -> [Expr]
generateTypeValueRulesFuncs = map dcValToExpr
  where
    dcValToExpr (dcs, v) =
      let
        xs = map (Name Ident "x" . Just) [0..]
        ts = map dcToType dcs
        v' = stripConstructor v
      in
      mkLams (map (uncurry Id) $ zip xs ts) (valToExpr v')

    stripConstructor (AppVal _ v@(LitVal _)) = v
    stripConstructor v = v

    dcToType (DC _ (TyFun t _)) = t
    dcToType _ = error "generateTypeValueRulesFuncs: Unsupported DC"

-- | Generates a function based on the DC/Val pairs.  Falls back on calling the
-- default function if none of the DC/Val pairs match.
generateTypeValueRulesFunc :: Id ->  [([DC], Val)] -> Expr
generateTypeValueRulesFunc def dcv =
  let
    arg_tys = argTypes def
    args = map (\(i, t) -> Id (Name SMT ("x" ++ show i) Nothing) t) $ zip ([0..] :: [Integer]) arg_tys
  in
  generateIfDCThenExprFunc args (mkApp $ Var def:map Var args) $ map (\(x, y) -> (x, valToExpr y)) dcv

generateInputTypeRulesFunc :: T.TypeEnv -> Id -> [(([DC], Maybe DC), [Example])] -> Expr
generateInputTypeRulesFunc tenv i =
  generateIfDCThenExprFunc args def . map generateFunctionCall
  where
    def = Var $ Id (Name SMT "Should be unreachable" Nothing) TYPE

    arg_tys = argTypes i
    args = map (\(i', t) -> Id (Name SMT ("x" ++ show i') Nothing) t) $ zip ([0..] :: [Integer]) arg_tys
    argsV = map Var args

    generateFunctionCall ((dcs, jdc), (e:_)) =
      let
        sels = map getSingleSelector dcs

        c = mkApp $ Var (func e):map (uncurry App) (zip sels argsV)
        c' = case jdc of
                  Just dc -> App (Data dc) c
                  Nothing -> c
      in
      (dcs, c')
    generateFunctionCall _ = error "generateInputTypeRulesFunc: no examples"

    getSingleSelector dc@(DC dcn _)
      | dct@(TyCon n _) <- returnType dc
      , Just (T.ADTSpec selectors) <- T.lookup n tenv
      , Just sel <- find (\s -> T.selectorDCName s == dcn) selectors
      , T.SelectorDC _ [nt] <- sel = Var $ Id (T.namedTypeName nt) (TyFun dct $ T.namedTypeType nt)
      | otherwise = error "Bad type"

generateIfDCThenExprFunc :: [Id] -> Expr -> [([DC], Expr)] -> Expr
generateIfDCThenExprFunc args def dcv =
  let
      -- Convert a list of ([DC], Val) into a list of (Expr, Val), where the
      -- Expr are boolean conditions such that, if satisfied, that Val should be
      -- returned
      testers_vals = mapFst (toTesters) dcv
      testers_apps = mapFst (toAppliedTesters args) testers_vals
      testers_anded = mapFst toAndedTesters testers_apps

      -- Combine the anded testers with ite's
      ret_type = returnType def
      ite = Var $ smtIte ret_type

      check_testers = foldr (\(ch, e) -> App (App (App ite ch) e)) def testers_anded
  in
  mkLams args $ check_testers
  where
    mapFst f = map (\(x, y) -> (f x, y))

    toTesters = map (Var . T.tester)
    toAppliedTesters as = map (\(arg, tester) -> App tester (Var arg)) . zip as
    toAndedTesters = foldr (\e1 -> App (App (Var smtAnd) e1)) (Data smtTrue)
