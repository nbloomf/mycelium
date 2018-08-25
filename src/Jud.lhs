---
title: Judgements
---

So far we've developed a grammar of expressions and a grammar of types and implemented a version of the Hindley-Milner type inference algorithm. Our goal is to use this as the object language for a natural deduction system so we can write machine-checked proofs about lambda calculus expressions. To that end, in this module we'll develop yet another grammar -- a grammar of _judgements_. These will be the atoms of logical proofs.

As usual we start with some module imports.

> {-# LANGUAGE LambdaCase, FlexibleInstances, BangPatterns #-}
> module Jud where
> 
> import Control.Monad
>   ( ap, foldM )
> import qualified Data.Map as M
>   ( elems, keysSet, filter, lookup )
> import Data.Proxy
>   ( Proxy(..) )
> import qualified Data.Set as S
>   ( Set(), insert, fromList, member, disjoint
>   , empty, singleton, unions, union, difference )
> import Test.QuickCheck
>   ( Arbitrary(..), Gen, getSize, elements, oneof, listOf1 )
> 
> import Var
> import Sub
> import Expr
> import Type
> import Infer



Judgements
----------

A _judgement_ is a statement which may be supported by evidence. What evidence means here is very narrow: an inference rule counts as evidence, as do assumptions made in the course of writing a proof. We'll get to evidence later though; first we need a concrete grammar of judgements.

Our judgements will be built from nine basic parts. (We can ignore the `Loc` parameter for now; these will be used later.)

First we have the basic logical connectives; variables, negation, conjunction, disjunction, implication, and equivalence. These have the usual meaning.

> data Jud
>   = JVar Loc (Var Jud)
>   | JNeg Loc Jud
>   | JConj Loc Jud Jud
>   | JDisj Loc Jud Jud
>   | JImpl Loc Jud Jud
>   | JEqui Loc Jud Jud

Next we have three connectives involving expressions.

>   | JEq Loc Expr Expr
>   | JIs Loc Expr String
>   | JAll Loc (Var Expr) Jud
>   deriving (Show)

_Equals_ represents the statement that two expressions have the same "value", whatever that means. We can interpret this judgement as a rewrite rule -- the left hand side of an equation can be rewritten to the right hand side, and vice versa.

The _is_ connective will be used to wrap complicated statements behind a name, like _injective_. It will have no introduction or elimination rules, and can only be introduced in a definition.

The _universal_ connective represents a judgement within which one expression variable is explicitly quantified with forall.

We haven't derived an `Eq` instance for `Jud`gements because we need it to account for renamings of the variable bound by foralls.

Here's an `Arbitrary` instance for judgements analogous to the ones for `Expr` and `MonoType`.

> instance Arbitrary Jud where
>   arbitrary = getSize >>= genDepth
>     where
>       genDepth :: Int -> Gen Jud
>       genDepth k
>         | k <= 0 = oneof
>             [ JVar <$> arbitrary <*> arbitrary
>             , JIs <$> arbitrary <*> arbitrary
>                 <*> (listOf1 $ elements _is_chars)
>             ]
>         | otherwise = do
>             let recur = genDepth =<< elements [0..(k-1)]
>             oneof
>               [ JNeg <$> arbitrary <*> recur
>               , JConj <$> arbitrary <*> recur <*> recur
>               , JDisj <$> arbitrary <*> recur <*> recur
>               , JImpl <$> arbitrary <*> recur <*> recur
>               , JEqui <$> arbitrary <*> recur <*> recur
>               , JEq <$> arbitrary <*> arbitrary <*> arbitrary
>               , JAll <$> arbitrary <*> arbitrary <*> recur
>               ]
> 
>   shrink = \case
>     JVar _ _ -> []
>     JNeg loc q -> q : map (JNeg loc) (shrink q)
>     JConj loc q1 q2 -> [ q1, q2 ] ++ shrink2 (JConj loc) q1 q2
>     JDisj loc q1 q2 -> [ q1, q2 ] ++ shrink2 (JDisj loc) q1 q2
>     JImpl loc q1 q2 -> [ q1, q2 ] ++ shrink2 (JImpl loc) q1 q2
>     JEqui loc q1 q2 -> [ q1, q2 ] ++ shrink2 (JEqui loc) q1 q2
>     JEq loc e1 e2 -> shrink2 (JEq loc) e1 e2
>     JIs _ _ _ -> []
>     JAll loc x q -> q : map (JAll loc x) (shrink q)
>     where
>       shrink2 f a b =
>         [ f u v | u <- shrink a, v <- shrink b ] ++
>         [ f u b | u <- shrink a ] ++
>         [ f a v | v <- shrink b ]
> 
> _is_chars = "abcdefghijklmnopqrstuvwxyz0123456789-_"
> 
> instance Arbitrary (Var Jud) where
>   arbitrary = do
>     let makeVar i = Var $ 'Q' : show i
>     k <- getSize
>     makeVar <$> elements [0..k]

Every judgement has a (possibly empty) set of free expression variables. Variables can only become bound via the `JAll` rule.

> freeExprVarsJ :: Jud -> S.Set (Var Expr)
> freeExprVarsJ = \case
>   JVar !loc _ -> S.empty
>   JNeg !loc p -> freeExprVarsJ p
>   JConj !loc p q -> S.union (freeExprVarsJ p) (freeExprVarsJ q)
>   JDisj !loc p q -> S.union (freeExprVarsJ p) (freeExprVarsJ q)
>   JImpl !loc p q -> S.union (freeExprVarsJ p) (freeExprVarsJ q)
>   JEqui !loc p q -> S.union (freeExprVarsJ p) (freeExprVarsJ q)
>   JEq !loc e f -> S.union (freeExprVars e) (freeExprVars f)
>   JIs !loc e _ -> freeExprVars e
> 
>   JAll !loc x q ->
>     S.difference (freeExprVarsJ q) (S.singleton x)

We need to be able to rename free expressions variables in a capture-avoiding way. As with expressions, this will generally change the meaning of a judgement but is useful as an intermediate step in computing alpha equivalence.

> renameFreeJ :: (Var Expr, Var Expr) -> Jud -> Jud
> renameFreeJ (u,v) = \case
>   JVar !loc x ->
>     JVar loc x
>   JNeg !loc p ->
>     JNeg loc (renameFreeJ (u,v) p)
>   JConj !loc p q ->
>     JConj loc (renameFreeJ (u,v) p) (renameFreeJ (u,v) q)
>   JDisj !loc p q ->
>     JDisj loc (renameFreeJ (u,v) p) (renameFreeJ (u,v) q)
>   JImpl !loc p q ->
>     JImpl loc (renameFreeJ (u,v) p) (renameFreeJ (u,v) q)
>   JEqui !loc p q ->
>     JEqui loc (renameFreeJ (u,v) p) (renameFreeJ (u,v) q)
>   JEq !loc e f ->
>     JEq loc (renameFreeExpr (u,v) e) (renameFreeExpr (u,v) f)
>   JIs !loc e m ->
>     JIs loc (renameFreeExpr (u,v) e) m
> 
>   JAll !loc x q -> if (x == u) || (x == v)
>     then
>       let
>         y = fresh
>           [ S.fromList [u,v]
>           , freeExprVarsJ q ]
>       in JAll loc y (renameFreeJ (u,v) $ renameFreeJ (x,y) q)
>     else JAll loc x (renameFreeJ (u,v) q)

The only interesting bit happens with `JAll`. If the dummy variable `x` is equal to either `u` or `v`, we first swap it out with a fresh variable to avoid capturing any occurrences in `q`.

Next we tackle renaming bound variables.

> renameBoundJ :: S.Set (Var Expr) -> Jud -> Jud
> renameBoundJ avoid = \case
>   JVar !loc x ->
>     JVar loc x
>   JNeg !loc p ->
>     JNeg loc (renameBoundJ avoid p)
>   JConj !loc p q ->
>     JConj loc (renameBoundJ avoid p) (renameBoundJ avoid q)
>   JDisj !loc p q ->
>     JDisj loc (renameBoundJ avoid p) (renameBoundJ avoid q)
>   JImpl !loc p q ->
>     JImpl loc (renameBoundJ avoid p) (renameBoundJ avoid q)
>   JEqui !loc p q ->
>     JEqui loc (renameBoundJ avoid p) (renameBoundJ avoid q)
>   JEq !loc e f ->
>     JEq loc (renameBoundExpr avoid e) (renameBoundExpr avoid f)
>   JIs !loc e m ->
>     JIs loc (renameBoundExpr avoid e) m
> 
>   JAll !loc x q -> if S.member x avoid
>     then
>       let
>         y = fresh [S.singleton x, freeExprVarsJ q, avoid]
>       in JAll loc y
>         (renameBoundJ avoid $ renameFreeJ (x,y) q)
>     else JAll loc x
>       (renameBoundJ avoid q)

These definitions make `Jud` an instance of `HasExprVars`.

> instance HasExprVars Jud where
>   freeExprVars = freeExprVarsJ
>   renameFreeExpr = renameFreeJ
>   renameBoundExpr = renameBoundJ

We're now prepared to define alpha equivalence on judgements. This is more or less the same as alpha equivalence for expressions.

> instance Eq Jud where
>   j1 == j2 = case (j1,j2) of
>     (JVar _ x1, JVar _ x2) -> x1 == x2
>     (JNeg _ p1, JNeg _ p2) -> p1 == p2
>     (JConj _ p1 q1, JConj _ p2 q2) -> (p1 == p2) && (q1 == q2)
>     (JDisj _ p1 q1, JDisj _ p2 q2) -> (p1 == p2) && (q1 == q2)
>     (JImpl _ p1 q1, JImpl _ p2 q2) -> (p1 == p2) && (q1 == q2)
>     (JEqui _ p1 q1, JEqui _ p2 q2) -> (p1 == p2) && (q1 == q2)
>     (JEq _ e1 f1, JEq _ e2 f2) -> (e1 == e2) && (f1 == f2)
>     (JIs _ e1 m1, JIs _ e2 m2) -> (e1 == e2) && (m1 == m2)
> 
>     (JAll _ x1 q1, JAll _ x2 q2) -> if x1 == x2
>       then q1 == q2
>       else
>         let
>           y = fresh
>             [ freeExprVars q1
>             , freeExprVars q2 ]
>         in
>           (renameFreeExpr (x1,y) q1) == (renameFreeExpr (x2,y) q2)
> 
>     _ -> False



Substitution
------------

We'll need to apply substitutions to judgements in two ways: for judgement variables and for expression variables. First we define substitution for expressions.

> instance SubExpr Jud where
>   s $> p = case p of
>     JVar !loc x -> JVar loc x
>     JNeg !loc q -> JNeg loc (s $> q)
>     JConj !loc q1 q2 -> JConj loc (s $> q1) (s $> q2)
>     JDisj !loc q1 q2 -> JDisj loc (s $> q1) (s $> q2)
>     JImpl !loc q1 q2 -> JImpl loc (s $> q1) (s $> q2)
>     JEqui !loc q1 q2 -> JEqui loc (s $> q1) (s $> q2)
>     JEq !loc e1 e2 -> JEq loc (s $> e1) (s $> e2)
>     JIs !loc e str -> JIs loc (s $> e) str
> 
>     JAll !loc x q ->
>       let
>         y = fresh
>           [ S.singleton x
>           , freeExprVars s
>           , support s
>           , freeExprVars q ]
>       in
>         JAll loc y (s $> (renameFreeExpr (x,y) q))

As usual the only interesting bits happen for the `JAll` rule, where we have to rename the bound variable to avoid capture.

Judgement substitutions inherit `SubExpr` and `HasExprVars` instances pointwise.

> instance SubExpr (Sub Jud) where
>   s $> (Sub m) = Sub $ fmap (s $>) m
> 
> instance HasExprVars (Sub Jud) where
>   freeExprVars (Sub m) =
>     S.unions . map freeExprVars . M.elems $ m
>   renameFreeExpr (u,v) (Sub m) =
>     Sub $ fmap (renameFreeExpr (u,v)) m
>   renameBoundExpr avoid (Sub m) =
>     Sub $ fmap (renameBoundExpr avoid) m

Next we handle substitutions for judgement variables; as with expression and type substitutions, we'll wrap this behind a type class. We also need an `Arbitrary` instance for judgement substitutions.

> class JudSub t where
>   ($~) :: Sub Jud -> t -> t
> 
> instance Arbitrary (Sub Jud) where
>   arbitrary = Sub <$> arbitrary
>   shrink (Sub m) = map Sub $ shrink m

We can apply judgement substitutions to judgements. This is made simpler by the fact that there are no binding constructs for judgement variables.

> instance JudSub Jud where
>   s $~ p = case p of
>     JVar !loc x -> case applySub x s of
>       Nothing -> JVar loc x
>       Just p' -> p'
>     JNeg !loc q -> JNeg loc $ s $~ q
>     JConj !loc q1 q2 -> JConj loc (s $~ q1) (s $~ q2)
>     JDisj !loc q1 q2 -> JDisj loc (s $~ q1) (s $~ q2)
>     JImpl !loc q1 q2 -> JImpl loc (s $~ q1) (s $~ q2)
>     JEqui !loc q1 q2 -> JEqui loc (s $~ q1) (s $~ q2)
>     JEq !loc e1 e2 -> JEq loc e1 e2
>     JIs !loc x str -> JIs loc x str
> 
>     JAll !loc x q ->
>       let
>         y = fresh
>           [ S.singleton x
>           , freeExprVars s
>           , freeExprVars q ]
>       in
>         JAll loc y (s $~ (renameFreeExpr (x,y) q))

Again in the `JAll` case we take care to avoid variable capture.

We can also apply judgement substitutions to judgement substitutions pointwise:

> instance JudSub (Sub Jud) where
>   s1 $~ (Sub m2) = Sub $ fmap (s1 $~) m2

And this can be turned into a monoid structure on the set of judgement substitutions.

> instance Semigroup (Sub Jud) where
>   s1 <> s2 = (s1 $~ s2) .& s1
>
> instance Monoid (Sub Jud) where
>   mempty = emptySub

Finally, 'judgement substitution application' should be a monoid action, which we can test.

> test_subjud_identity
>   :: (JudSub t, Eq t) => Proxy t -> t -> Bool
> test_subjud_identity _ j =
>   j == emptySub $~ j
> 
> test_subjud_action
>   :: (JudSub t, Eq t) => Proxy t -> Sub Jud -> Sub Jud -> t -> Bool
> test_subjud_action _ s1 s2 j =
>   (s1 $~ (s2 $~ j)) == ((s1 <> s2) $~ j)



Matching
--------

We will need to _match_ one judgement against another, as we did with `Expr`s. Eventually we'll express _inference rules_ in terms of judgements, and matching is how we'll detect when a given inference rule is applied correctly.

A judgement matching consists of two substitutions: a judgement substitution and an expression substitution. If $J_1$ and $J_2$ are matched by $S_J$ and $S_E$, then $$J_2 = S_J \cdot (S_E \cdot J_1).$$ We can construct matchings by case analysis. As with expression matching, we'll need to keep track of a bound variable context along the way.

> matchJud :: Jud -> Jud -> Maybe (Sub Jud, Sub Expr)
> matchJud = matchJud' S.empty
>   where
>     match2 bound (p1,q1) (p2,q2) = do
>       (js1,es1) <- matchJud' bound p1 p2
>       (js2,es2) <- matchJud' bound q1 q2
>       js <- unionSub js1 js2
>       es <- unionSub es1 es2
>       Just (js,es)

First a utility: to match pairs of judgements, we match corresponding judgements and combine.

>     matchJud' bound j1 j2 = case (j1,j2) of
>       (JVar _ x, p) -> if S.disjoint bound (freeExprVars p)
>         then Just (x --> p, emptySub)
>         else Nothing

Judgement variables match any judgement, as long as no free variables become bound in context.

>       (JNeg _ p1, JNeg _ p2) ->
>         matchJud' bound p1 p2
>       (JConj _ p1 q1, JConj _ p2 q2) ->
>         match2 bound (p1,q1) (p2,q2)
>       (JDisj _ p1 q1, JDisj _ p2 q2) ->
>         match2 bound (p1,q1) (p2,q2)
>       (JImpl _ p1 q1, JImpl _ p2 q2) ->
>         match2 bound (p1,q1) (p2,q2)
>       (JEqui _ p1 q1, JEqui _ p2 q2) ->
>         match2 bound (p1,q1) (p2,q2)

The logical connectives don't bind any new variables, so matching proceeds recursively using the `match2` utility.

>       (JEq _ e1 f1, JEq _ e2 f2) -> do
>         es1 <- matchExprInContext bound e1 e2
>         es2 <- matchExprInContext bound f1 f2
>         es <- unionSub es1 es2
>         Just (emptySub, es)

For equations, we match either side with the bound variable context and union.

>       (JIs _ e1 m1, JIs _ e2 m2) ->
>         if m1 == m2
>           then do
>             es <- matchExprInContext bound e1 e2
>             Just (emptySub, es)
>           else Nothing

Is statements are similar to equations; match the expressions with the bound context.

>       (JAll _ x1 q1, JAll _ x2 q2) ->
>         if x1 == x2
>           then matchJud' (S.insert x1 bound) q1 q2
>           else do
>             let
>               y = fresh
>                 [ bound
>                 , S.fromList [x1,x2]
>                 , freeExprVars q1
>                 , freeExprVars q2 ]
>             matchJud'
>              (S.insert y bound)
>              (renameFreeExpr (x1,y) q1)
>              (renameFreeExpr (x2,y) q2)

`JAll`s are similar to lambda expressions.

>       _ -> Nothing

And no other pairs of judgements match.

Judgement matching is a fundamental part of proof checking, so we'd do well to test it thoroughly.

> test_cases_jud_match :: Bool
> test_cases_jud_match = and
>   [ (==)
>       (matchJud
>         (JVar Q (Var "P"))
>         (JEq Q (EVar Q (Var "x")) (EVar Q (Var "y"))))
>       (Just
>         ( Var "P" --> (JEq Q (EVar Q (Var "x")) (EVar Q (Var "y")))
>         , emptySub))

This case matches the judgement variable $P$ against the judgement $x = y$.

>   , (==)
>       (matchJud
>         (JConj Q
>           (JVar Q (Var "P"))
>           (JEq Q
>             (EVar Q (Var "x1"))
>             (EVar Q (Var "x2"))))
>         (JConj Q
>           (JIs Q (EVar Q (Var "x0")) "crunchy")
>           (JEq Q
>             (ELam Q (Var "x0") (EVar Q (Var "x0")))
>             (EVar Q (Var "x2")))))
>       (Just
>         ( Var "P" --> (JIs Q (EVar Q (Var "x0")) "crunchy")
>         , (Var "x1" --> (ELam Q (Var "x0") (EVar Q (Var "x0"))))
>           .& (Var "x2" --> EVar Q (Var "x2"))))

This case matches the judgement $$P \wedge (x_1 = x_2)$$ against $$(x_0\ \mathrm{is\ crunchy}) \wedge ((\lambda x_0 . x_0) = x_2)$$

>   , (==)
>       (matchJud
>         (JImpl Q (JVar Q (Var "P")) (JVar Q (Var "P")))
>         (JImpl Q (JVar Q (Var "Q")) (JVar Q (Var "P"))))
>       Nothing

This case attempts to match $P \Rightarrow P$ against $Q \Rightarrow P$, which should fail.

>   , (==)
>       (matchJud
>         (JAll Q (Var "k")
>           (JVar Q (Var "p")))
>         (JAll Q (Var "z")
>           (JEq Q (EVar Q (Var "z")) (EVar Q (Var "x")))))
>       Nothing
>   ]

This case attempts to match a judgement variable inside a universally quantified statement against another universally quantified statement where the bound variable occurs. This should fail, because it is not possible to substitute a judgement for $P$ that correctly captures the bound variable.

Property tests are also useful here; the trick is thinking of useful properties. We can of course test the equational property of matching; if $S_J$ and $S_E$ are a matching for $J_1$ and $J_2$, then we should have $$J_2 = S_J \cdot (S_E \cdot J_1).$$

> test_jud_match
>   :: Jud -> Jud -> Bool
> test_jud_match j1 j2 =
>   case matchJud j1 j2 of
>     Nothing -> True
>     Just (js,es) -> j2 == js $~ (es $> j1)

This test should pass if our implementation of `matchJud` is correct. The bad news is that the vast majority of generated test cases will hit the `Nothing` branch and pass trivially. To get some better coverage we'll need to cook up some pairs of judgements that are set up to match.

The simplest example I can think of is that every judgement should match itself via a trivial substitution on its set of free variables.

> test_jud_match_self
>   :: Jud -> Bool
> test_jud_match_self j =
>   case matchJud j j of
>     Nothing -> False
>     Just (_, es@(Sub m)) -> and
>       [ (M.keysSet m) == (freeExprVars j)
>       , trivialExprSub es
>       ]

Barely less trivially, every judgement should still match itself after we rename the bound variables.

> test_jud_match_rename_bound
>   :: S.Set (Var Expr) -> Jud -> Bool
> test_jud_match_rename_bound avoid j =
>   case matchJud j (renameBoundExpr avoid j) of
>     Nothing -> False
>     Just (_, es@(Sub m)) -> and
>       [ (M.keysSet m) == (freeExprVars j)
>       , trivialExprSub es
>       ]

Another way to cook up judgements that match is to make one an explicit substitution of the other; $J$ should match $S_J \cdot (S_E \cdot J)$ for any $J$, $S_E$ and $S_J$.

> test_jud_match_sub
>   :: Sub Jud -> Sub Expr -> Jud -> Bool
> test_jud_match_sub js1 es1 j =
>   case matchJud j (js1 $~ (es1 $> j)) of
>     Nothing -> False
>     Just (js2,es2) ->
>       (js2 $~ (es2 $> j)) == (js1 $~ (es1 $> j))



Type Checking
-------------

Finally, we can also check that the expressions in a judgement can be consistently typed.

> instance TypeCheck Jud where
>   typeCheck jud env = case jud of 
>     JVar _ _ -> return env
>     JNeg _ q -> typeCheck q env
>     JConj _ p q -> typeCheck p env >>= typeCheck q
>     JDisj _ p q -> typeCheck p env >>= typeCheck q
>     JImpl _ p q -> typeCheck p env >>= typeCheck q
>     JEqui _ p q -> typeCheck p env >>= typeCheck q
>     JEq _ e f -> do
>       env2 <- introTypeVars (S.union (freeExprVars e) (freeExprVars f)) env
>       (se,te) <- infer env2 e
>       let env3 = se $. env2
>       (sf,tf) <- infer env3 f
>       let env4 = sf $. env3
>       case unifyTypes te tf of
>         Left err -> throwU err
>         Right w -> return (w $. env4)
>     JIs _ e _ -> do
>       env2 <- introTypeVars (freeExprVars e) env
>       (se,_) <- infer env2 e
>       return (se $. env2)
>     JAll _ x q -> do
>       let TypeEnv m = env
>       case M.lookup (Right x) m of
>         Nothing ->
>           introTypeVar x env
>             >>= typeCheck q
>             >>= elimTypeVar x
>         Just _ -> do
>           let
>             y = fresh
>               [ S.singleton x
>               , typedVarsIn env
>               , freeExprVars q ]
>           introTypeVar y env
>             >>= typeCheck (renameFreeExpr (x,y) q)
>             >>= elimTypeVar y
