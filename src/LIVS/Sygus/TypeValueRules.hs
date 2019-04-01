-- should we call this ExampleGrouping or something instead?
module LIVS.Sygus.TypeValueRules ( typeValueRules
                                 , typeTypeRules
                                 , inputTypeRules
                                 , filterNotRuleCovered
                                 , generateRulesFunc ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Sygus.SMTPrims

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S

import Control.Applicative

-- | Split a list of exmaples into lists of examples of matching types
--  :: [Example] -> [[Example]]

-- | 
inputTypeRules :: [Example] -> [([DC], Maybe DC)]
inputTypeRules exs = let
    ttRules = HM.map Just $ HM.fromList $ typeTypeRules exs
    rs = HM.fromList $ map ((\(dcs,_) -> (dcs,Nothing)). buildRule) exs
  in
    HM.toList $ HM.unionWith (<|>) rs ttRules


-- | Establish rules about which input types always lead to the same output type
typeTypeRules :: [Example] -> [([DC], DC)]
typeTypeRules es = let
    rs = map ((\(dcs,v) -> (dcs, valToDC v)). buildRule) es
  in 
    filterRules' rs

-- | Establish rules about which input types that always lead to the same value
--   Identifies which input types generate an error value (or any fixed value)
typeValueRules :: [Example] -> [([DC],Val)]
typeValueRules es = let
    rs = map buildRule es
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

buildRule :: Example -> ([DC],Val)
buildRule e =
    (map valToDC $ input e, output e)

valToDC :: Val -> DC
valToDC v = case (appValCenter v) of
    DataVal dc -> dc
    LitVal l -> error $ "Bad call: had LitVal"++(show l)
    AppVal _ _-> error "Bad call: had AppVal"

-- | From a list of examples, removes all those already covered by one of the rules
filterNotRuleCovered :: [([DC],Val)] -> [Example] -> [Example]
filterNotRuleCovered dcv = filter (flip notElem dcv . buildRule)

-- | Generates a function based on the DC/Val pairs.  Falls back on calling the
-- default function if none of the DC/Val pairs match.
generateRulesFunc :: Id ->  [([DC], Val)] -> Expr
generateRulesFunc def dcv =
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
