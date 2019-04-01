module LIVS.Sygus.TypeValueRules ( typeValueRules
                                 , filterNotRuleCovered
                                 , generateRulesFunc ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Sygus.SMTPrims

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.List

-- | Establish rules about which input types that always lead to the same value
--   Identifies which input types generate an error value (or any fixed value)
typeValueRules :: [Example] -> [([DC],Val)]
typeValueRules es = let
    rs = map buildRule es
  in
    filterRules S.empty HM.empty rs

filterRules :: S.HashSet [DC] -> HM.HashMap [DC] Val -> [([DC],Val)] -> [([DC],Val)]
filterRules reject provisionalKeep ((dc,v):rs) = 
    if S.member dc reject || (HM.lookupDefault v dc provisionalKeep /= v)
    then filterRules (S.insert dc reject) (HM.delete dc provisionalKeep) rs
    else filterRules reject (HM.insert dc v provisionalKeep) rs
filterRules reject provisionalKeep [] = HM.toList provisionalKeep 

buildRule :: Example -> ([DC],Val)
buildRule e =
    (map (valToDC . appValCenter) $ input e, output e)
  where
    valToDC v = case v of
      DataVal dc -> dc
      _ -> error "Bad call"

-- | From a list of examples, removes all those already covered by one of the rules
filterNotRuleCovered :: [([DC],Val)] -> [Example] -> [Example]
filterNotRuleCovered dcv = filter (flip notElem dcv . buildRule)

-- | Generates a function based on the DC/Val pairs.  Falls back on calling the
-- default function if none of the DC/Val pairs match.
generateRulesFunc :: Id ->  [([DC], Val)] -> Expr
generateRulesFunc def dcv =
  let
      arg_tys = argTypes def
      args = map (\(i, t) -> Id (IdentName $ "x" ++ show i) t) $ zip ([0..] :: [Integer]) arg_tys

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