---
title: Tests
---

This module collects the tests for our proof checker in one place; to run the entire suite use `stack test`.

> {-# LANGUAGE FlexibleContexts #-}
> module Main where
> 
> import Data.Proxy
>   ( Proxy(..) )
> import System.Exit
>   ( exitFailure )
> import Test.QuickCheck
>   ( Arbitrary(..), quickCheckResult, quickCheckWithResult
>   , maxSize, maxSuccess, Args, stdArgs, Testable )
> import Test.QuickCheck.Test
>   ( isSuccess )
> 
> import Var
> import Sub
> import Expr
> import Type
> import Infer
> import Jud
> import Proof
> import Module
> import Fancy
> import Parser
 
> main :: IO ()
> main = do
>   let args1 = stdArgs { maxSuccess = 50000, maxSize = 30 }
>   let args2 = stdArgs { maxSuccess = 20000, maxSize = 20 }
>   let args3 = stdArgs { maxSuccess = 10000, maxSize = 10 }
> 
>   test_Sub args1
>   test_Expr args3
>   test_Type args2
>   test_Infer args2
>   test_Jud args2
>   test_Proof args2
>   test_Module args3
>   test_Fancy args3
>   test_Parser args3
> 
> test :: (Testable prop) => prop -> IO ()
> test prop = do
>   result <- quickCheckResult prop
>   case isSuccess result of
>     True -> return ()
>     False -> exitFailure
> 
> testWith :: (Testable prop) => Args -> prop -> IO ()
> testWith args prop = do
>   result <- quickCheckWithResult args prop
>   case isSuccess result of
>     True -> return ()
>     False -> exitFailure



Substitutions
-------------

We bundle together substitution tests parameterized on a `Proxy` type for easy reuse.

> _Sub_properties
>   :: (Eq t, Show t, Arbitrary t, Arbitrary (Var t), Arbitrary (Sub t))
>   => Args -> String -> Proxy t -> IO ()
> _Sub_properties args name p = do
>   putStrLn $ ">>>>> Sub properties: " ++ name
> 
>   putStrLn "====> Support of an empty substitution"
>   test $
>     test_support_empty_sub p
> 
>   putStrLn "====> Support of a singleton substitution"
>   testWith args $
>     test_support_singleton p
>
>   putStrLn "====> Apply the empty substitution"
>   testWith args $
>     test_sub_lookup_empty p
> 
>   putStrLn "====> Apply a singleton substitution"
>   testWith args $
>     test_sub_lookup_singleton p
> 
>   putStrLn "====> Identity property for unionSub"
>   testWith args $
>     test_sub_union_identity p
> 
>   putStrLn "====> Idempotent property for unionSub"
>   testWith args $
>     test_sub_union_idempotent p
> 
>   putStrLn "====> Commutative property for unionSub"
>   testWith args $
>     test_sub_union_commutative p
> 
>   putStrLn "====> Associative property for unionSub"
>   testWith args $
>     test_sub_union_associative p
> 
>   putStrLn "====> unionSub on singletons"
>   testWith args $
>     test_sub_union_nothing p
> 
>   putStrLn "====> Support of a union"
>   testWith args $
>     test_sub_union_support p
> 
>   putStrLn "====> Identity property for extension"
>   testWith args $
>     test_sub_extend_empty p
> 
>   putStrLn "====> Idempotent property for extension"
>   testWith args $
>     test_sub_extend_idempotent p
> 
>   putStrLn "====> Left zero property for extension on singletons"
>   testWith args $
>     test_sub_extend_singleton p
> 
>   putStrLn "====> Associative property for extension"
>   testWith args $
>     test_sub_extend_associative p
> 
>   putStrLn "====> Support of an extension"
>   testWith args $
>     test_sub_extend_support p
> 
>   putStrLn "====> Identity property for undefine"
>   testWith args $
>     test_undefine_identity p
> 
>   putStrLn "====> Action property for undefine"
>   testWith args $
>     test_undefine_action p
> 
>   putStrLn "====> undefine on singletons"
>   testWith args $
>     test_undefine_singleton p

Now for tests of the whole module.

> test_Sub :: Args -> IO ()
> test_Sub args = do
>   putStrLn "\n--- Sub"
> 
>   _Sub_properties args "Int"
>     (Proxy :: Proxy Int)



Expressions
-----------

We bundle the properties of renaming expression variables for easy reuse.

> _HasExprVars_properties
>   :: (HasExprVars t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _HasExprVars_properties args name p = do
>   putStrLn $ ">>>>> HasExprVars properties: " ++ name
> 
>   putStrLn "====> Rename: free property"
>   testWith args $ test_exprvars_rename_free p
> 
>   putStrLn "====> Rename: transposition property"
>   testWith args $ test_exprvars_rename_trans p
> 
>   putStrLn "====> Rename: bound property"
>   testWith args $ test_exprvars_rename_bound p
> 
>   putStrLn "====> Rename: bound equality"
>   testWith args $ test_exprvars_rename_eq p

We bundle the properties of `Eq` for easy reuse.

> _Eq_properties
>   :: (Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _Eq_properties args name p = do
>   putStrLn $ ">>>>> Eq properties: " ++ name
> 
>   putStrLn "====> Expr equality is reflexive"
>   testWith args $ test_eq_reflexive p
> 
>   putStrLn "====> Expr equality is symmetric"
>   testWith args $ test_eq_symmetric p
> 
>   putStrLn "====> Expr equality is transitive"
>   testWith args $ test_eq_transitive p

And we bundle the properties of `Monoid` for reuse.

> _Monoid_properties
>   :: (Monoid t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _Monoid_properties args name p = do
>   putStrLn $ ">>>>> Monoid properties: " ++ name
>   putStrLn "====> Monoid: Identity law"
>   testWith args $ test_monoid_identity p
> 
>   putStrLn "====> Monoid: Associativity law"
>   testWith args $ test_monoid_associative p

And for the monoid action properties of `SubExpr`.

> _SubExpr_properties
>   :: (SubExpr t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _SubExpr_properties args name p = do
>   putStrLn $ ">>>>> SubExpr properties: " ++ name
> 
>   putStrLn "====> Identity law for Sub Expr action on Expr"
>   testWith args $
>     test_subexpr_identity p
> 
>   putStrLn "====> Associativity law for Sub Expr action on Expr"
>   testWith args $
>     test_subexpr_action p

Now for tests of the module.

> test_Expr :: Args -> IO ()
> test_Expr args = do
>   putStrLn "\n--- Expr"
> 
>   putStrLn "====> Freshness property for constants"
>   testWith args $
>     test_fresh_not_member (Proxy :: Proxy (Con Expr))
> 
>   putStrLn "====> Freshness property for variables"
>   testWith args $
>     test_fresh_not_member (Proxy :: Proxy (Var Expr))
> 
>   putStrLn "====> Expr: free variables test cases"
>   test test_cases_freeExprVars
> 
>   putStrLn "====> Expr: equality test cases"
>   test test_cases_expr_eq
> 
>   _Eq_properties args "Expr"
>     (Proxy :: Proxy Expr)
> 
>   _HasExprVars_properties args "Expr"
>     (Proxy :: Proxy Expr)
> 
>   _Sub_properties args "Expr"
>     (Proxy :: Proxy Expr)
> 
>   _HasExprVars_properties args "Sub Expr"
>    (Proxy :: Proxy (Sub Expr))
> 
>   putStrLn "====> Expr substitution test cases"
>   test test_cases_sub_expr
> 
>   _Monoid_properties args "Sub Expr"
>     (Proxy :: Proxy (Sub Expr))
> 
>   _SubExpr_properties args "Expr"
>     (Proxy :: Proxy Expr)
> 
>   _SubExpr_properties args "Sub Expr"
>     (Proxy :: Proxy (Sub Expr))
> 
>   putStrLn "====> Matching: Expr test cases"
>   test test_cases_expr_match
> 
>   putStrLn "====> Matching: Expr substitution property"
>   testWith args test_expr_match_sub
>
>   putStrLn "====> Matching: Expr transitive property"
>   testWith args test_expr_match_transitive
>
>   putStrLn "====> Matching: Expr match self"
>   testWith args test_expr_match_self
>
>   putStrLn "====> Matching: Expr match rename"
>   testWith args test_expr_match_rename
>  
>   putStrLn "====> Matching: Expr with explicit substitution"
>   testWith args test_expr_sub_match



Types
-----

We bundle the properties of `SubMono` for reuse.

> _SubMono_properties
>   :: (SubMono t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _SubMono_properties args name p = do
>   putStrLn $ ">>>>> SubMono properties: " ++ name
> 
>   putStrLn "====> Identity law for SubMono on MonoType"
>   testWith args $ test_submono_identity p
> 
>   putStrLn "====> Action law for SubMono on MonoType"
>   testWith args $ test_submono_action p

And properties of `UnifyTypes`:

> _UnifyTypes_properties
>   :: (UnifyTypes t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _UnifyTypes_properties args name p = do
>   putStrLn $ ">>>>> UnifyTypes properties: " ++ name
> 
>   putStrLn "====> Substitution property for unify"
>   testWith args $ test_unify_eq p
> 
>   putStrLn "====> Self property for unify"
>   testWith args $ test_unify_self_empty p
> 
>   putStrLn "====> Commutative property for unify"
>   testWith args $ test_unify_symmetric p
> 
>   putStrLn "====> Closure property for unify"
>   testWith args $ test_unify_down_closed p

Now for the module tests.

> test_Type :: Args -> IO ()
> test_Type args = do
>   putStrLn "\n--- Type"
> 
>   putStrLn "====> Freshness property for constants"
>   testWith args $
>     test_fresh_not_member (Proxy :: Proxy (Con MonoType))
> 
>   putStrLn "====> Freshness property for variables"
>   testWith args $
>     test_fresh_not_member (Proxy :: Proxy (Var MonoType))
> 
>   _Sub_properties args "MonoType"
>     (Proxy :: Proxy MonoType)
> 
>   _Monoid_properties args "Sub MonoType"
>     (Proxy :: Proxy (Sub MonoType))
> 
>   _SubMono_properties args "MonoType"
>     (Proxy :: Proxy MonoType)
> 
>   _SubMono_properties args "Sub MonoType"
>     (Proxy :: Proxy (Sub MonoType))
> 
>   _UnifyTypes_properties args "MonoType"
>     (Proxy :: Proxy MonoType)
> 
>   putStrLn "====> Test cases: polytype equality"
>   test test_cases_polytype_eq
> 
>   _Eq_properties args "PolyType"
>     (Proxy :: Proxy PolyType)
> 
>   putStrLn "====> PolyType equality rename property"
>   testWith args test_polytype_eq_renames
> 
>   _SubMono_properties args "PolyType"
>     (Proxy :: Proxy PolyType)
> 
>   putStrLn "====> PolyType: unification test cases"
>   test test_cases_unify_polytype
> 
>   _UnifyTypes_properties args "PolyType"
>     (Proxy :: Proxy PolyType)



Infer
-----

We bundle the property tests for `TypeCheck` for reuse.

> _TypeCheck_properties
>   :: (TypeCheck t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _TypeCheck_properties args name p = do
>   putStrLn $ ">>>>> TypeCheck properties: " ++ name
> 
>   putStrLn "====> TypeCheck: free variables have a type"
>   testWith args $ test_typecheck_free_vars p
> 
>   putStrLn "====> TypeCheck: renaming bound vars"
>   testWith args $ test_typecheck_bound_vars p
> 
>   putStrLn "====> TypeCheck: renaming free vars"
>   testWith args $ test_typecheck_rename_free p

Now the module tests.

> test_Infer :: Args -> IO ()
> test_Infer args = do
>   putStrLn "\n--- Infer"
> 
>   _SubMono_properties args "TypeEnv"
>     (Proxy :: Proxy TypeEnv)
> 
>   _UnifyTypes_properties args "TypeEnv"
>     (Proxy :: Proxy TypeEnv)
> 
>   putStrLn "====> Type inference test cases"
>   test test_cases_infer
> 
>   putStrLn "====> G |-S e : t => SG |-S e : St"
>   testWith args test_infer_sub
> 
>   putStrLn "====> TypeCheck test cases: Expr"
>   test test_cases_typecheck_expr
> 
>   _TypeCheck_properties args "Expr"
>     (Proxy :: Proxy Expr)



Judgements
----------

We package the monoid action property tests of judgement substitution for easy reuse.

> _SubJud_properties
>   :: (JudSub t, Eq t, Show t, Arbitrary t)
>   => Args -> String -> Proxy t -> IO ()
> _SubJud_properties args name p = do
>   putStrLn $ ">>>>> SubJud properties: " ++ name
> 
>   putStrLn "====> Identity law for Sub Jud action"
>   testWith args $ test_subjud_identity p
> 
>   putStrLn "====> Associativity law for Sub Jud action"
>   testWith args $ test_subjud_action p

Tests for the module:

> test_Jud :: Args -> IO ()
> test_Jud args = do
>   putStrLn "\n--- Jud"
> 
>   putStrLn "====> Freshness property for variables"
>   testWith args $
>     test_fresh_not_member (Proxy :: Proxy (Var Jud))
> 
>   _HasExprVars_properties args "Jud"
>     (Proxy :: Proxy Jud)
> 
>   _Eq_properties args "Jud"
>     (Proxy :: Proxy Jud)
> 
>   _SubExpr_properties args "Jud"
>     (Proxy :: Proxy Jud)
> 
>   _SubExpr_properties args "Sub Jud"
>     (Proxy :: Proxy (Sub Jud))
> 
>   _HasExprVars_properties args "Sub Jud"
>     (Proxy :: Proxy (Sub Jud))
> 
>   _Monoid_properties args "Sub Jud"
>     (Proxy :: Proxy (Sub Jud))
> 
>   _SubJud_properties args "Jud"
>     (Proxy :: Proxy Jud)
> 
>   _SubJud_properties args "Sub Jud"
>     (Proxy :: Proxy (Sub Jud))
> 
>   putStrLn "====> Matching: Jud test cases"
>   test test_cases_jud_match
> 
>   putStrLn "====> Matching: Jud substitution property"
>   testWith args test_jud_match
> 
>   putStrLn "====> Matching: Jud self match"
>   testWith args test_jud_match_self
> 
>   putStrLn "====> Matching: Jud rename bound vars"
>   testWith args test_jud_match_rename_bound
> 
>   putStrLn "====> Matching: Jud explicit substitution"
>   testWith args test_jud_match_sub
> 
>   _TypeCheck_properties args "Jud"
>     (Proxy :: Proxy Jud)



Proofs
------

> test_Proof :: Args -> IO ()
> test_Proof args = do
>   putStrLn "\n--- Proof"
> 
>   putStrLn "====> Matching: Rule substitution property"
>   testWith args test_match_rule
> 
>   putStrLn "====> Matching: Rule self property"
>   testWith args test_match_rule_self
> 
>   putStrLn "====> Matching: Rule explicit substitution"
>   testWith args test_match_rule_sub
> 
>   _HasExprVars_properties args "Rule"
>     (Proxy :: Proxy Rule)
> 
>   _TypeCheck_properties args "Rule"
>     (Proxy :: Proxy Rule)
> 
>   putStrLn "====> Rule typecheck test cases"
>   test test_cases_rule_typecheck
> 
>   _HasExprVars_properties args "HypEnv"
>     (Proxy :: Proxy HypEnv)
> 
>   _HasExprVars_properties args "Assumptions"
>     (Proxy :: Proxy Assumptions)
> 
>   _Monoid_properties args "Assumptions"
>     (Proxy :: Proxy Assumptions)



Module
------

> test_Module :: Args -> IO ()
> test_Module args = do
>   putStrLn "\n--- Module"
> 
>   putStrLn "====> Proof Checking: Toys"
>   test test_toy_theory



Fancy
-----

> test_Fancy :: Args -> IO ()
> test_Fancy args = do
>   putStrLn "\n--- Fancy"
> 
>   putStrLn "====> Deserialization"
>   testWith args test_deserialize



Parsing
-------

> test_Parser :: Args -> IO ()
> test_Parser args = do
>   putStrLn "\n--- Parser"
> 
>   putStrLn "====> Basic Syntax: Var Expr"
>   testWith args $ test_prettybasic (Proxy :: Proxy (Var Expr))
> 
>   putStrLn "====> Test cases: parse Var Expr"
>   test test_cases_parse_varexpr
> 
>   putStrLn "====> Basic Syntax: Con Expr"
>   testWith args $ test_prettybasic (Proxy :: Proxy (Con Expr))
> 
>   putStrLn "====> Test cases: parse Con Expr"
>   test test_cases_parse_conexpr
> 
>   putStrLn "====> Basic Syntax: Expr"
>   testWith args $ test_prettybasic (Proxy :: Proxy Expr)
> 
>   putStrLn "====> Test cases: parse Expr"
>   test test_cases_parse_expr
> 
>   putStrLn "====> Basic Syntax: Var MonoType"
>   testWith args $ test_prettybasic (Proxy :: Proxy (Var MonoType))
> 
>   putStrLn "====> Test cases: parse Var MonoType"
>   test test_cases_parse_varmonotype
> 
>   putStrLn "====> Basic Syntax: Con MonoType"
>   testWith args $ test_prettybasic (Proxy :: Proxy (Con MonoType))
> 
>   putStrLn "====> Test cases: parse Con MonoType"
>   test test_cases_parse_conmonotype
> 
>   putStrLn "====> Basic Syntax: MonoType"
>   testWith args $ test_prettybasic (Proxy :: Proxy MonoType)
> 
>   putStrLn "====> Test cases: parse MonoType"
>   test test_cases_parse_monotype
> 
>   putStrLn "====> Basic Syntax: PolyType"
>   testWith args $ test_prettybasic (Proxy :: Proxy PolyType)
> 
>   putStrLn "====> Test cases: parse PolyType"
>   test test_cases_parse_polytype
> 
>   putStrLn "====> Basic Syntax: Sub Expr"
>   testWith args $ test_prettybasic (Proxy :: Proxy (Sub Expr))
> 
>   putStrLn "====> Test cases: parse Sub Expr"
>   test test_cases_parse_subexpr
> 
>   putStrLn "====> Basic Syntax: Var Jud"
>   testWith args $ test_prettybasic (Proxy :: Proxy (Var Jud))
> 
>   putStrLn "====> Test cases: parse Var Jud"
>   test test_cases_parse_varjud
> 
>   putStrLn "====> Basic Syntax: Jud"
>   testWith args $ test_prettybasic (Proxy :: Proxy Jud)
> 
>   putStrLn "====> Test cases: parse Var Jud"
>   test test_cases_parse_varjud
> 
>   putStrLn "====> Basic Syntax: HypName"
>   testWith args $ test_prettybasic (Proxy :: Proxy HypName)
> 
>   putStrLn "====> Basic Syntax: RuleName"
>   testWith args $ test_prettybasic (Proxy :: Proxy RuleName)
> 
>   putStrLn "====> Basic Syntax: Rule"
>   testWith args $ test_prettybasic (Proxy :: Proxy Rule)
> 
>   putStrLn "====> Fancy Syntax: Rule"
>   testWith args $ test_prettyfancy (Proxy :: Proxy Rule)
> 
>   putStrLn "====> Test cases: parse Rule (Basic)"
>   test test_cases_parse_rule_basic
> 
>   putStrLn "====> Test cases: parse Rule (Fancy)"
>   test test_cases_parse_rule_fancy
> 
>   putStrLn "====> Basic Syntax: Proof"
>   testWith args $ test_prettybasic (Proxy :: Proxy Proof)
> 
>   putStrLn "====> Basic Syntax: FancyProofLine"
>   testWith args $ test_prettybasic (Proxy :: Proxy FancyProofLine)
> 
>   putStrLn "====> Basic Syntax: FancyProof"
>   testWith args $ test_prettybasic (Proxy :: Proxy FancyProof)
> 
>   putStrLn "====> Fancy Syntax: Proof"
>   testWith args $ test_prettyfancy (Proxy :: Proxy Proof)
> 
>   putStrLn "====> Basic Syntax: Claim"
>   testWith args $ test_prettybasic (Proxy :: Proxy Claim)
> 
>   putStrLn "====> Basic Syntax: Module"
>   testWith args $ test_prettybasic (Proxy :: Proxy Module)
