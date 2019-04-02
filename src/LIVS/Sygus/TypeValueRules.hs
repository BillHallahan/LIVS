-- should we call this ExampleGrouping or something instead?
module LIVS.Sygus.TypeValueRules ( typeValueRules
                                 , filterNotTypeValueRuleCovered

                                 , typeTypeRules
                                 , inputTypeRules
                                 , simplifyExamples

                                 , generateTypeValueRulesFunc ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Sygus.SMTPrims

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S

import Control.Applicative

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
    simplifyExample' e@(Example { input = is, output = out }) =
        let
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

-- | Generates a function based on the DC/Val pairs.  Falls back on calling the
-- default function if none of the DC/Val pairs match.
generateTypeValueRulesFunc :: Id ->  [([DC], Val)] -> Expr
generateTypeValueRulesFunc def dcv =
  let
      arg_tys = argTypes def
      args = map (\(i, t) -> Id (Name SMT ("x" ++ show i) Nothing) t) $ zip ([0..] :: [Integer]) arg_tys

      -- Convert a list of ([DC], Val) into a list of (Expr, Val), where the
      -- Expr are boolean conditions such that, if satisfied, that Val should be
      -- returned
      testers_vals = mapFst (toTesters) dcv
      testers_apps = mapFst (toAppliedTesters args) testers_vals
      testers_anded = mapFst toAndedTesters testers_apps

      tester_expr = mapSnd valToExpr testers_anded

      -- Combine the anded testers with ite's
      ret_type = returnType def
      ite = Var $ smtIte ret_type

      def_call = mkApp $ Var def:map Var args
      check_testers = foldr (\(ch, e) -> App (App (App ite ch) e)) def_call tester_expr 
  in
  error $ show check_testers
  where
    mapFst f = map (\(x, y) -> (f x, y))
    mapSnd f = map (\(x, y) -> (x, f y))

    toTesters = map (Var . T.tester)
    toAppliedTesters as = map (\(arg, tester) -> App tester (Var arg)) . zip as
    toAndedTesters = foldr (\e1 -> App (App (Var smtAnd) e1)) (Data smtTrue)
