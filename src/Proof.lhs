---
title: Proofs
---

We're now prepared to define what a _proof_ is and what it means for a proof to be valid. We'll be using a basic [natural deduction](https://en.wikipedia.org/wiki/Natural_deduction) style of proof. In this style, proofs are rose trees of judgements, where each node is annotated with _evidence_. Evidence takes the form of _inference rules_. Each production rule for the judgement grammar gets one or more _introduction rules_ that serve as evidence for statements that include a new instance of the production, as well as one or more _elimination rules_ that serve as evidence for decomposing a judgement. Here's an example of an inference rule.

$$\begin{array}{ccc}
P &            & Q \\ \hline
  & P \wedge Q &
\end{array}$$

The symbols above the line are called _premises_ and the one below is the _conclusion_. This rule says "if we have evidence for $P$, and also evidence for $Q$, then we have evidence for $P \wedge Q$". The $P$ and $Q$ here are judgement variables. Natural deduction proofs are trees of statements like this, with each "node" in the tree supported by an inference rule.

As usual we start with some module imports.

> {-# LANGUAGE LambdaCase #-}
> module Proof where
> 
> import Control.Monad
>   ( ap, foldM )
> import Control.Monad.Loops
>   ( concatM )
> import Data.List
>   ( groupBy, sortBy, nub )
> import qualified Data.Map as M
> import qualified Data.Set as S
> import Test.QuickCheck
> 
> import Var
> import Sub
> import Expr
> import Type
> import Infer
> import Jud



Rules
-----

An _inference rule_ consists of a _conclusion_ and zero or more _premises_, where the conclusion and premises are judgements.

> data Rule
>   = Rule Jud [Jud]
>   deriving (Eq, Show)

We can make an `Arbitrary` instance for rules. The vast majority of rules it generates will be nonsense.

> instance Arbitrary Rule where
>   arbitrary = Rule <$> arbitrary <*> arbitrary
> 
>   shrink (Rule q ps) =
>     [ Rule q' ps' | q' <- shrink q, ps' <- shrink ps ] ++
>     [ Rule q ps' | ps' <- shrink ps ] ++
>     [ Rule q' ps | q' <- shrink q ]

The most important operation on rules is _matching_. Inference rules are _proof schemas_, representing many concrete proofs. A rule can be applied to a particular conclusion and list of premises if there is a substitution from the rule to the candidate judgements.

> matchRule :: Rule -> Jud -> [Jud] -> Maybe (Sub Jud, Sub Expr)
> matchRule (Rule a as) b bs = matchList (a:as, b:bs)
>   where
>     matchList :: ([Jud],[Jud]) -> Maybe (Sub Jud, Sub Expr)
>     matchList = \case
>       ([],[]) ->
>         return (emptySub, emptySub)
>       (u:us,v:vs) -> do
>         (js1,es1) <- matchJud u v
>         (js2,es2) <- matchList (us,vs)
>         js <- unionSub js1 js2
>         es <- unionSub es1 es2
>         return (js, es)
>       _ -> Nothing

Note that matching rules imposes an order on the premises. Most authors on natural deduction say that the order of premises for an inference rule doesn't matter, but allowing rearrangements of the premises would make matching much more complicated -- so we just won't do that :).

We can test `matchRule` a couple of different ways. The most obvious one is that if a rule matches a given list of judgements, then the substitution should carry the rule to the judgements.

> test_match_rule
>   :: Rule -> Jud -> [Jud] -> Bool
> test_match_rule r@(Rule cr hrs) ct hts =
>   case matchRule r ct hts of
>     Nothing -> True
>     Just (js,es) ->
>       let
>         ok a b = a == js $~ (es $> b)
>       in and
>         [ ok ct cr
>         , length hrs == length hts
>         , and $ zipWith ok hts hrs
>         ]

This test doesn't carry a lot of confidence, because the vast majority of generated test cases are useless.

Another check is that rules should match themselves.

> test_match_rule_self
>   :: Rule -> Bool
> test_match_rule_self r@(Rule c hs) =
>   case matchRule r c hs of
>     Nothing -> False
>     Just (_,es) -> trivialExprSub es

And if we apply a substitution to a rule, it should match the result.

> test_match_rule_sub
>   :: Rule -> Sub Jud -> Sub Expr -> Bool
> test_match_rule_sub r@(Rule c hs) js es =
>   let s x = js $~ (es $> x) in
>   case matchRule r (s c) (map s hs) of
>     Nothing -> False
>     Just _ -> True

In one sense a `Rule` is just a list of judgements, which makes it easy to define `HasExprVars` and `TypeCheck` instances.

> instance HasExprVars Rule where
>   freeExprVars (Rule c hs) =
>     mconcat $ map freeExprVars (c:hs)
>   renameBoundExpr avoid (Rule c hs) =
>     Rule (renameBoundExpr avoid c) (map (renameBoundExpr avoid) hs)
>   renameFreeExpr (u,v) (Rule c hs) =
>     Rule (renameFreeExpr (u,v) c) (map (renameFreeExpr (u,v)) hs)
> 
> instance TypeCheck Rule where
>   typeCheck (Rule c hs) env = concatM (map typeCheck (c:hs)) env

For funsies, let's see an example. From the rule

$$\begin{array}{ccc}
 \\ \hline
 xy = z
\end{array}$$

we infer that $y$ has type $a$, $z$ has type $b$, and $x$ has type $a \rightarrow b$.

> test_cases_rule_typecheck :: Bool
> test_cases_rule_typecheck = and
>   [ _typecheck_and_unify
> 
>     (Rule
>       (JEq Q
>         (EApp Q (EVar Q (Var "x")) (EVar Q (Var "y")))
>         (EVar Q (Var "z")))
>       [])
> 
>     (TypeEnv $ M.fromList
>       [ (Right $ Var "x", ForAll S.empty
>           (TArr Q (TVar Q (Var "a")) (TVar Q (Var "b"))))
>       , (Right $ Var "y", ForAll S.empty
>           (TVar Q (Var "a")))
>       , (Right $ Var "z", ForAll S.empty
>           (TVar Q (Var "b")))
>       ])
>   ]

Inference rules will end up playing a role similar to axioms and theorems. We'll have a bunch of them we consider "valid" for some reason and are allowed to match them against proofs. With this in mind, we define a _rule environment_ to be a set of named rules.

> data RuleEnv = RuleEnv
>   { theRuleEnv :: M.Map RuleName Rule
>   } deriving (Eq, Show)
> 
> data RuleName = RuleName String
>   deriving (Eq, Ord, Show)
> 
> instance Arbitrary RuleName where
>   arbitrary = RuleName <$> (listOf1 $ elements _rulename_chars)
> 
> _rulename_chars = concat
>   [ "abcdefghijklmnopqrstuvwxyz"
>   , "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
>   , "0123456789-_"
>   ]



Proof
-----

A natural deduction style proof is essentially a labeled rose tree of judgements; the nodes in the tree are _supported judgements_, and each node is labeled with a _justification_. We can define this with a type; the full details are a little more complicated than 'labeled rose tree' because certain labels are special forms that need to be dealt with differently.

> data Proof
>   = Use Loc RuleName Jud [Proof]

We will eventually need to have introduction and elimination rules for each judgement constructor. But many of these can be expressed in essentially the same way that we would express a theorem at the user level. For instance, the introduction rule for $\wedge$. These are collectively handled by `Use`. Other rules will require special syntactic support, and these have to be built into the definition of proof. For example!

>   | Hyp Loc HypName Jud
>   | Dis Loc HypName Jud Proof

The `Hyp`othesis and `Dis`charge proofs together comprise the introduction rule for $\Rightarrow$, and have to be dealt with outside of the usual rule-matching strategy because they involve state. Typically discharging is explained something like this:

$$\begin{array}{ccc}
 P \\
 \vdots \\
 Q \\ \hline
 P \Rightarrow Q
\end{array}$$

The elipses are doing a lot of work here. The idea is that $P$ is introduced as a named hypothesis somewhere above $Q$, and this is discharged as $P \Rightarrow Q$ but not before. The "but not before" part is the state; when validating a proof from the leaves to the root, we have to keep track of which hypotheses have been introduced and which have already been discharged.

>   | ElimEq Loc Jud (Var Expr) Jud Proof Proof
>   | IntroEq Loc Jud

The `ElimEq` rule is what justifies substituting equals for equals in a judgement. Schematically it looks like this:

$$\begin{array}{ccc}
s = t &                   & \Phi[x \mapsto s] \\ \hline
      & \Phi[x \mapsto t] &
\end{array}$$

Where [square brackets] denote a substitution; $\Phi[x \mapsto s]$ is obtained by replacing all free occurrences of the expression variable $x$ in $\Phi$ by the expression $s$. This substitution is not part of the judgement syntax itself, but rather a kind of metasyntax; that's why this rule needs to be dealt with separately. `IntroEq` is the introduction rule for equality; it can be defined with `Use` (it doesn't require any syntactic support) but it will be handy to build this into the syntax.

>   | IntroU Loc Jud (Var Expr) (Var Expr) Proof
>   | ElimU Loc Jud (Var Expr) Expr Proof

`IntroU` and `ElimU` are the introduction and elimination rules for universal quantifiers; these also need a special syntax because they come with _side conditions_ on correctness. The introduction rule is schematically

$$\begin{array}{c}
\Phi \\ \hline
\forall x . \Phi[u \mapsto x]
\end{array}$$

with the side condition that $x$ is not free in $\Phi$ and $u$ is not free in any assumptions or undischarged hypotheses. The elimination rule is

$$\begin{array}{c}
\forall x . \Phi \\ \hline
\Phi[x \mapsto u]
\end{array}$$

These side conditions are another kind of contextual state, which is why these need to be handled separately.

>   | IntroE Loc Jud (Var Expr) Expr Proof
>   | ElimE Loc Jud (Var Expr) (Var Expr) Proof Proof

`IntroE` and `ElimE` are the introduction and elimination rules for existential quantifiers. Schematically, `IntroE` is

$$\begin{array}{c}
\Phi[u \mapsto e] \\ \hline
\exists u . \Phi
\end{array}$$

while `ElimE` is

$$\begin{array}{c}
\exists x. \Phi & & \Phi[x \mapsto u] \Rightarrow \Psi \\ \hline
 & \Psi &
\end{array}$$

with the side conditions that $u$ does not occur in $\exists x . \Phi$, in $\Psi$, or in any undischarged hypotheses or assumptions in the proof of $\Phi[x \mapsto u] \Rightarrow \Psi$.

>   | Subst Loc Jud (Sub Expr) Proof

The `Subst`itution proof is a little different. Free variables in a proof denote a specific but arbitrary object. This is different from a variable bound by a forall, which denotes _every_ object of the appropriate type. As such, it makes sense to perform substitutions on the free variables. Schematically, that looks something like this:

$$\begin{array}{c}
\Phi[S] \\ \hline
S \cdot \Phi
\end{array}$$

Again, [square brackets] indicate a metasyntactic substitution; $\Phi$ is a judgement with (maybe) some free variables, and $S \cdot \Phi$ is the result of applying some substitution to $\Phi$. Substitution is not really either an introduction or an elimination rule.

>   | Assume Loc Int Jud
>   deriving (Show)

The final proof type is the assumption. Assumptions are similar to hypotheses in that they let us introduce a judgement with no explicit support. However, hypotheses must eventually be discharged, while assumptions are _never_ discharged. To see the difference, suppose we were trying to prove a rule like the following.

$$\begin{array}{ccc}
R &                 & Q \\ \hline
  & P \Rightarrow Q &
\end{array}$$

(This is nonsense, just go with it.) In the proof tree for this rule, $Q$ is an assumption; it's one of the premises of the rule being proved. $P$ appears as the antecedent of an implies judgement in the conclusion. Somewhere in the proof tree, $P$ is introduced as a hypothesis and then _discharged_ to support $P \Rightarrow Q$, but $P$ is not one of the premises of the rule.

And that's it; every step in a proof has one of these forms. It looks a little puny. What about the other logical connectives? Everything we need to say about them can be expressed as an atomic inference rule, and does not need to be baked in to our definition of proof. This means our proof checker can be pretty flexible -- we can, for example, decide later whether or not to allow some rules, like the law of the excluded middle.

For testing, we'll need an `Eq` instance for `Proof` that ignores `Loc` parameters.

> instance Eq Proof where
>   p1 == p2 = case (p1,p2) of
>     (Assume _ k1 p1, Assume _ k2 p2) ->
>       (k1 == k2) && (p1 == p2)
>     (Hyp _ n1 p1, Hyp _ n2 p2) ->
>       (n1 == n2) && (p1 == p2)
>     (Dis _ n1 q1 p1, Dis _ n2 q2 p2) ->
>       (n1 == n2) && (p1 == p2) && (q1 == q2)
>     (IntroEq _ e1, IntroEq _ e2) ->
>       (e1 == e2)
>     (ElimEq _ q1 x1 e1 p1 u1, ElimEq _ q2 x2 e2 p2 u2) ->
>       (q1 == q2) && (x1 == x2) && (e1 == e2) && (p1 == p2) && (u1 == u2)
>     (IntroU _ q1 x1 y1 p1, IntroU _ q2 x2 y2 p2) ->
>       (q1 == q2) && (x1 == x2) && (y1 == y2) && (p1 == p2)
>     (ElimU _ q1 x1 e1 p1, ElimU _ q2 x2 e2 p2) ->
>       (q1 == q2) && (x1 == x2) && (e1 == e2) && (p1 == p2)
>     (IntroE _ q1 x1 e1 p1, IntroE _ q2 x2 e2 p2) ->
>       (q1 == q2) && (x1 == x2) && (e1 == e2) && (p1 == p2)
>     (ElimE _ q1 x1 y1 u1 v1, ElimE _ q2 x2 y2 u2 v2) ->
>       (q1 == q2) && (x1 == x2) && (y1 == y2) && (u1 == u2) && (v1 == v2)
>     (Subst _ q1 s1 p1, Subst _ q2 s2 p2) ->
>       (q1 == q2) && (s1 == s2) && (p1 == p2)
>     (Use _ n1 q1 p1, Use _ n2 q2 p2) ->
>       (n1 == n2) && (q1 == q2) && (p1 == p2)
>     _ -> False

And here's an `Arbitrary` instance.

> instance Arbitrary Proof where
>   arbitrary = getSize >>= genDepth
>     where
>       genDepth k
>         | k <= 0 = oneof
>             [ Assume <$> arbitrary <*> (abs <$> arbitrary) <*> arbitrary
>             , Hyp <$> arbitrary <*> arbitrary <*> arbitrary
>             ]
>         | otherwise = do
>             let recur = genDepth =<< elements [0..(k-1)]
>             oneof
>               [ Dis <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> recur
>               , IntroEq <$> arbitrary <*> arbitrary
>               , ElimEq <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> arbitrary <*> recur <*> recur
>               , Subst <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> recur
>               , IntroU <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> arbitrary <*> recur
>               , ElimU <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> arbitrary <*> recur
>               , IntroE <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> arbitrary <*> recur
>               , ElimE <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> arbitrary <*> recur <*> recur
>               , Use <$> arbitrary <*> arbitrary <*> arbitrary
>                   <*> listOf recur
>               ]
> 
>   shrink = \case
>     Assume loc k q -> map (Assume loc k) $ shrink q
>     Hyp loc n q -> map (Hyp loc n) $ shrink q
>     Dis loc n q p ->
>       [ p ] ++
>       [ Dis loc n q' p' | q' <- shrink q, p' <- shrink p ] ++
>       [ Dis loc n q p' | p' <- shrink p ] ++
>       [ Dis loc n q' p | q' <- shrink q ]
>     IntroEq loc j ->
>       [ IntroEq loc q | q <- shrink j ]
>     ElimEq loc u x v p q ->
>       [ p, q ] ++
>       [ ElimEq loc u' x v' p' q' |
>         u' <- shrink u, v' <- shrink v, p' <- shrink p, q' <- shrink q ]
>     Subst loc w s p ->
>       [ p ] ++
>       [ Subst loc w' s' p' |
>         w' <- shrink w, s' <- shrink s, p' <- shrink p ]
>     IntroU loc q x y p ->
>       [ p ] ++
>       [ IntroU loc q' x y p' |
>         q' <- shrink q, p' <- shrink p ]
>     ElimU loc q x e p ->
>       [ p ] ++
>       [ ElimU loc q' x e' p' |
>         q' <- shrink q, e' <- shrink e, p' <- shrink p ]
>     IntroE loc q x y p ->
>       [ p ] ++
>       [ IntroE loc q' x y p' |
>         q' <- shrink q, p' <- shrink p ]
>     ElimE loc q x e p u ->
>       [ p ] ++
>       [ ElimE loc q' x e' p' u' |
>         q' <- shrink q, e' <- shrink e, p' <- shrink p, u' <- shrink u ]
>     Use loc name p ps ->
>       ps ++
>       [ Use loc name p' ps' |
>         p' <- shrink p, ps' <- shrink ps ]



Verification
------------

We've defined what a proof is; now let's tackle what it means for a proof to be valid.

Proof checking requires dealing with effects of a few kinds.

* Handling errors when things go wrong
* A read-only environment of allowed inference rules
* A mutable state holding the undischarged hypotheses
* A write-only log of the assumptions used

This is a job for monads.

First we introduce types for the hypothesis environment; this will help us keep track of which hypotheses have been introduced but not discharged.

> data HypEnv = HypEnv
>   { theHypEnv :: M.Map HypName Jud
>   } deriving (Eq, Show)
> 
> data HypName = HypName String
>   deriving (Eq, Ord, Show)
> 
> instance Arbitrary HypName where
>   arbitrary = HypName <$> (listOf1 $ elements _hypname_chars)
> 
> _hypname_chars = concat
>   [ "abcdefghijklmnopqrstuvwxyz"
>   , "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
>   , "0123456789-_"
>   ]
> 
> instance HasExprVars HypEnv where
>   freeExprVars (HypEnv hs) =
>     S.unions $ map freeExprVars $ M.elems hs
>   renameFreeExpr (u,v) (HypEnv hs) =
>     HypEnv $ M.map (renameFreeExpr (u,v)) hs
>   renameBoundExpr avoid (HypEnv hs) =
>     HypEnv $ M.map (renameBoundExpr avoid) hs
> 
> instance Arbitrary HypEnv where
>   arbitrary = HypEnv <$> arbitrary
> 
>   shrink (HypEnv hs) = map HypEnv $ shrink hs

We also need a structure to keep track of what assumptions have been made. This will be the log type for a writer monad. It's important that we also keep track of whether the same number has been used to encode two different assumptions.

> data Assumptions
>   = Assumptions (M.Map Int Jud) (S.Set Int)
>   deriving (Eq, Show)
> 
> instance HasExprVars Assumptions where
>   freeExprVars (Assumptions as _) =
>     S.unions $ map freeExprVars $ M.elems as
>   renameFreeExpr (u,v) (Assumptions as ws) =
>     Assumptions (M.map (renameFreeExpr (u,v)) as) ws
>   renameBoundExpr avoid (Assumptions as ws) =
>     Assumptions (M.map (renameBoundExpr avoid) as) ws
> 
> instance Arbitrary Assumptions where
>   arbitrary = Assumptions <$> arbitrary <*> arbitrary
> 
>   shrink (Assumptions m ks) =
>     [ Assumptions n ls | n <- shrink m, ls <- shrink ks ] ++
>     [ Assumptions m ls | ls <- shrink ks ] ++
>     [ Assumptions n ks | n <- shrink m ]

Assumptions need to be a `Monoid` as well.

> instance Semigroup Assumptions where
>   (Assumptions m1 k1) <> (Assumptions m2 k2) =
>     Assumptions (M.union m1 m2) $
>       S.unions
>         [ k1, k2
>         , S.filter (\k -> M.lookup k m1 /= M.lookup k m2) $
>           S.intersection (M.keysSet m1) (M.keysSet m2)
>         ]
> 
> instance Monoid Assumptions where
>   mempty = Assumptions mempty mempty

Now `Check` is a hand rolled stack of reader, writer, error, and state monads.

> data Check a = Check
>   { runCheck
>       :: (RuleEnv, HypEnv)
>       -> Either VerifyError (a, (HypEnv, Assumptions))
>   }

The monad instance for `Check` is standard stuff.

> instance Monad Check where
>   return a = Check $ \(_,hs) ->
>     Right (a, (hs, mempty))
> 
>   x >>= f = Check $ \(rs,hs) ->
>     case runCheck x (rs,hs) of
>       Left err -> Left err
>       Right (a, (hs', w1)) ->
>         case runCheck (f a) (rs,hs') of
>           Left err -> Left err
>           Right (b, (hs'', w2)) ->
>             Right (b, (hs'', w1 <> w2))
> 
> instance Applicative Check where
>   pure = return
>   (<*>) = ap
> 
> instance Functor Check where
>   fmap f x = x >>= (return . f)

So `Check a` represents a computation that can read from a rule environment, can alter a hypothesis environment, and will return either an `a` with an assumption log or a verification error.

We need a few helpers. First one that throws a verification error:

> checkError :: VerifyError -> Check a
> checkError err = Check $ \_ -> Left err

We also have a rogues gallery of things that can go wrong with a proof.

> data VerifyError
>   = HypAlreadyDefined HypName Jud
>   | HypNotFound HypName
>   | HypNotDischarged [HypName]
>   | MalformedDischarge Loc Jud
>   | BadSubstitution (Sub Expr)
>   | RuleNotFound RuleName
>   | MalformedSubstitution Loc
>   | RuleDoesNotMatch Loc RuleName Rule [Jud]
>   | ReusedAssumptions (S.Set Int)
>   | ProofDoesNotMatch Rule Jud [Jud]
>   | RuleAlreadyDefined RuleName
>   | TypeAlreadyDefined PolyType
>   | FreeVariableInPremise Loc (Var Expr)
>   | BindingFreeVar Loc (Var Expr) Jud
>   | EqExpected Loc
>   | NotEqual Loc
>   | BadEqSubstitutionRHS Loc
>   | BadEqSubstitutionLHS Loc
>   | MalformedIntroU Loc
>   | MalformedElimU Loc
>   | MalformedIntroE Loc
>   | SomeVarMismatch Loc
>   | SomeSubMismatch Loc
>   | AllExpected Loc
>   | MalformedElimE Loc
>   | ElimEBindVar Loc
>   | AllVarMismatch Loc (Var Expr) (Var Expr)
>   | TypeUnificationError UnificationError
>   | InferenceError TypeError
>   deriving (Eq, Show)

A helper for adding a new hypothesis to the environment, making sure its name is unique:

> introHyp :: HypName -> Jud -> Check ()
> introHyp name p = Check $ \(_, HypEnv hs) ->
>   case M.lookup name hs of
>     Nothing ->
>       Right ((), (HypEnv $ M.insert name p hs, mempty))
>     Just q ->
>       if q == p
>         then Right ((), (HypEnv hs, mempty))
>         else Left $ HypAlreadyDefined name p

A helper for logging an assumption:

> assume :: Int -> Jud -> Check ()
> assume k p = Check $ \(_,hs) ->
>   Right ((), (hs, Assumptions (M.fromList [(k,p)]) mempty))

A helper for discharging a hypothesis:

> dischargeHyp :: HypName -> Check Jud
> dischargeHyp name = Check $ \(_, HypEnv hs) ->
>   case M.lookup name hs of
>     Nothing ->
>       Left $ HypNotFound name
>     Just j ->
>       Right (j, (HypEnv $ M.delete name hs, mempty))

A helper for looking up a rule in the environment.

> lookupRule :: RuleName -> Check Rule
> lookupRule name = Check $ \(RuleEnv rs, hs) ->
>   case M.lookup name rs of
>     Nothing -> Left $ RuleNotFound name
>     Just r -> Right (r, (hs, mempty))

And a helper for checking that a variable is unused in the undischarged premises of a proof.

> unusedInHyp :: Loc -> Var Expr -> Check a -> Check a
> unusedInHyp loc x m = Check $ \(rs, hs) ->
>   case runCheck m (rs,hs) of
>     Left err -> Left err
>     Right (a, (hs, as)) ->
>       if (S.member x (freeExprVars hs))
>            || (S.member x (freeExprVars as))
>         then Left $ FreeVariableInPremise loc x
>         else Right (a, (hs, as))

We're finally prepared to check a proof. The result of checking the proof will be the _conclusion_ of the theorem statement.

> checkProof :: Proof -> Check Jud
> checkProof = \case
>   Assume _ k p -> do
>     assume k p
>     return p

Assumptions are valid evidence of themselves. Note that we also add the assumption to the environment.

>   Hyp _ name p -> do
>     introHyp name p
>     return p

Hypotheses are also valid evidence of themselves; but note that we add the name and judgement to the current hypothesis environment.

>   Dis loc name w pf -> do
>     q <- checkProof pf
>     p <- dischargeHyp name
>     if w == (JImpl Q p q)
>       then return (JImpl Q p q)
>       else checkError $ MalformedDischarge loc w

To check a discharge proof, we recursively check its child proof and look up and discharge the corresponding hypothesis before returning an implication judgement.

>   ElimEq loc w x p pe pf -> do
>     eq <- checkProof pe
>     case eq of
>       JEq _ lhs rhs -> do
>         q <- checkProof pf
>         if q == (x --> lhs) $> p
>           then if w == (x --> rhs) $> p
>             then return $ (x --> rhs) $> p
>             else checkError $ BadEqSubstitutionRHS loc
>           else checkError $ BadEqSubstitutionLHS loc
>       _ -> checkError $ EqExpected loc
> 
>   IntroEq loc q -> do
>     case q of
>       JEq loc' e1 e2 -> if e1 == e2
>         then return $ JEq loc' e1 e2
>         else checkError $ NotEqual loc
>       _ -> checkError $ EqExpected loc

The equality elimination and introduction rules need to ensure we've given proofs of the correct form.

>   Subst loc w s pf -> do
>     q <- checkProof pf
>     if w == s $> q
>       then return (s $> q)
>       else checkError $ MalformedSubstitution loc

The substitution proof just checks syntactic equality.

>   IntroU loc w x y pf -> do
>     q <- unusedInHyp loc x $ checkProof pf
>     if S.member y (freeExprVars q)
>       then checkError $ BindingFreeVar loc y q
>       else if w == JAll loc y ((x --> EVar loc y) $> q)
>         then return $ JAll loc y ((x --> EVar loc y) $> q)
>         else checkError $ MalformedIntroU loc
> 
>   ElimU loc w x e pf -> do
>     q <- checkProof pf
>     case q of
>       JAll _ z p ->
>         if x == z
>           then if w == (x --> e) $> p
>             then return $ (x --> e) $> p
>             else checkError $ MalformedElimU loc
>           else checkError $ AllVarMismatch loc x z
>       _ -> checkError $ AllExpected loc

The universal introduction and elimination rules need to check their respective side conditions.

>   IntroE loc w x e pf -> do
>     q <- checkProof pf
>     case w of
>       JSome _ y p -> do
>         if x == y
>           then if q == (x --> e) $> p
>             then return w
>             else checkError $ SomeSubMismatch loc
>           else checkError $ SomeVarMismatch loc
>       _ -> checkError $ MalformedIntroE loc
> 
>   ElimE loc w u x pe pi -> do
>     qe <- checkProof pe
>     qi <- unusedInHyp loc u $ checkProof pi
>     case (qe, qi) of
>       (JSome _ y pe, JImpl _ pi m) ->
>         if y == x
>           then if pi == (x --> (EVar Q u)) $> pe
>             then if (S.member u (freeExprVars pe))
>                    || (S.member u (freeExprVars m))
>               then checkError $ ElimEBindVar loc
>               else if w == m
>                 then return w
>                 else checkError $ MalformedElimE loc
>             else checkError $ MalformedElimE loc
>           else checkError $ SomeVarMismatch loc

The existential introduction and elimination rules need to check their respective side conditions.

>   Use loc name c ps -> do
>     hs <- mapM checkProof ps
>     r <- lookupRule name
>     case matchRule r c hs of
>       Nothing -> checkError $ RuleDoesNotMatch loc name r (c:hs)
>       Just _ -> return c

Finally we have `Use`; these proofs are checked by recursively checking the child proofs and then verifying that the named rule matches.

And with that, we can express and check proofs. The `check` function

1. recursively checks all nodes in the proof;
2. ensures that all hypotheses are discharged;
3. and verifies that the assumptions are numbered consistently

before returning the conclusion and premises of the proof.

> check :: RuleEnv -> Proof -> Either VerifyError (Jud, [Jud])
> check rules proof =
>   case runCheck (checkProof proof) (rules, HypEnv M.empty) of
>     Left err -> Left err
>     Right (j, (HypEnv hs, Assumptions as ks)) -> if not $ M.null hs
>       then Left $ HypNotDischarged $ M.keys hs
>       else if not $ S.null ks
>         then Left $ ReusedAssumptions ks
>         else Right (j, M.elems as)

`validate` takes the proof check one step further, comparing the conclusion and premises of a proof to some rule.

> validate :: RuleEnv -> Rule -> Proof -> Either VerifyError ()
> validate env (Rule cr ars) pf = do
>   (ct, ats) <- check env pf
>   if (ct == cr) && (ats == ars)
>     then return ()
>     else Left $ ProofDoesNotMatch (Rule cr ars) ct ats



Types
-----

We can also type check proofs.

> checkTypes :: Proof -> TypeEnv -> Infer TypeEnv
> checkTypes proof env = case proof of
>   Assume _ _ q -> typeCheck q env
>   Hyp _ _ q -> typeCheck q env
> 
>   Dis _ _ w pf -> concatM
>     [ typeCheck w
>     , checkTypes pf
>     ] env
>   IntroEq _ p -> typeCheck p env
>   ElimEq _ w x q pe pf -> concatM
>     [ typeCheck w
>     , typeCheck q
>     , checkTypes pe
>     , checkTypes pf
>     ] env
>   Subst _ w s pf -> concatM
>     [ typeCheck w
>     , checkTypes pf
>     ] env
>   IntroU _ w x y pf -> concatM
>     [ typeCheck w
>     , checkTypes pf
>     ] env
>   ElimU _ w x e pf -> concatM
>     [ typeCheck w
>     , checkTypes pf
>     ] env
>   IntroE _ w x e pf -> concatM
>     [ typeCheck w
>     , checkTypes pf
>     ] env
>   ElimE _ w u x pe pi -> concatM
>     [ typeCheck w
>     , checkTypes pe
>     , checkTypes pi
>     ] env
>   Use _ n q pfs -> concatM
>     ( typeCheck q : map checkTypes pfs ) env

We just need a utility for lifting inference errors to verification errors.

> liftInfer :: Infer a -> Either VerifyError a
> liftInfer x = case execInfer x of
>   Left (Left err) -> Left $ TypeUnificationError err
>   Left (Right err) -> Left $ InferenceError err
>   Right a -> return a



Claims
------

An _axiom_ is a rule we accept without proof, while a _theorem_ is a rule we accept only with a valid proof. Collectively axioms and theorems are called _claims_.

> data Claim
>   = Axiom RuleName Rule
>   | Theorem RuleName Rule Proof
>   | TypeDecl (Con Expr) MonoType
>   deriving (Eq, Show)
> 
> instance Arbitrary Claim where
>   arbitrary = do
>     k <- arbitrary :: Gen Int
>     case k`mod`3 of
>       0 -> Axiom <$> arbitrary <*> arbitrary
>       1 -> Theorem <$> arbitrary <*> arbitrary <*> arbitrary
>       _ -> TypeDecl <$> arbitrary <*> arbitrary

A _theory_ is a list of claims with the property that proofs only refer to named claims appearing earlier in the list. If the proof of a rule is valid, it can be added to the rule environment.

> addRule :: RuleName -> Rule -> RuleEnv -> Either VerifyError RuleEnv
> addRule name rule (RuleEnv m) =
>   case M.lookup name m of
>     Nothing -> Right $ RuleEnv $ M.insert name rule m
>     Just _ -> Left $ RuleAlreadyDefined name
> 
> addType
>   :: Con Expr -> MonoType -> TypeEnv -> Either VerifyError TypeEnv
> addType x t env@(TypeEnv m) =
>   case M.lookup (Left x) m of
>     Nothing -> Right $ TypeEnv $ M.insert (Left x) (generalize env t) m
>     Just _ -> Left $ TypeAlreadyDefined (generalize env t)
> 
> checkClaim
>   :: (TypeEnv, RuleEnv) -> Claim
>   -> Either VerifyError (TypeEnv, RuleEnv)
> checkClaim (typeEnv, ruleEnv) claim = case claim of
>   Axiom name rule -> do
>     ruleEnv' <- addRule name rule ruleEnv
>     liftInfer $ typeCheck rule typeEnv
>     return (typeEnv, ruleEnv')
>   Theorem name rule proof -> do
>     validate ruleEnv rule proof
>     liftInfer $ checkTypes proof typeEnv
>     ruleEnv' <- addRule name rule ruleEnv
>     return (typeEnv, ruleEnv')
>   TypeDecl x t -> do
>     typeEnv' <- addType x t typeEnv
>     return (typeEnv', ruleEnv)

We can also check an entire list of claims, adding each to the rule environment as it is checked.

> checkClaims
>   :: (TypeEnv, RuleEnv) -> [Claim]
>   -> Either VerifyError (TypeEnv, RuleEnv)
> checkClaims env cs = case cs of
>   [] -> return env
>   a:as -> do
>     env' <- checkClaim env a
>     checkClaims env' as
