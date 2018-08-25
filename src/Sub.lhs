---
title: Substitutions
---

Two fundamental operations on grammars with variables are _substitution_ and _unification_.

A _substitution_ for a grammar is a mapping from variables to expressions, which can be _applied_ to a concrete expression. Exactly how substitutions are applied depends on the details of the grammar, but even without knowing those details we can develop a useful algebra of substitutions.

_Unification_ corresponds to a kind of factorization on expressions.

As usual we start with some module imports.

> {-# LANGUAGE FlexibleInstances #-}
> module Sub where
> 
> import qualified Data.Map as M
>   ( Map(..), empty, fromList, union, lookup
>   , difference, fromSet, keys )
> import qualified Data.Map.Merge.Lazy as M
>   ( mergeA, zipWithAMatched, traverseMissing )
> import Data.Proxy
>   ( Proxy(Proxy) )
> import qualified Data.Set as S
>   ( Set(..), fromList, singleton
>   , empty, union, disjoint )
> import Test.QuickCheck
>   ( Arbitrary(..) )
>
> import Var



As Mappings
-----------

A _substitution_ over a grammar `t` is a mapping from variables over `t` to arbitrary values of type `t`; we can represent this using the standard library `Map` type.

> data Sub t
>   = Sub (M.Map (Var t) t)
>   deriving (Eq, Show)

And for the sake of testing, here's a representative `Arbitrary` instance for variables and substitutions over the `Int` "grammar".

> instance Arbitrary (Var Int) where
>   arbitrary = Var <$> arbitrary
> 
> instance Arbitrary (Sub Int) where
>   arbitrary = Sub <$> arbitrary
>   shrink (Sub m) = map Sub $ shrink m

The fundamental thing we do with substitutions is _apply_ them; this has a signature like $$\mathsf{Sub}\ t \times t \rightarrow t.$$ That is the signature of an _action_. In practice substitution should also act on itself, and should form a monoid, and the application of substitutions to arbitrary things is in fact a _monoid action_, which is saying something very nice.

At this level of generality, though, we can't express these properties in a useful way without bringing in some language extensions I prefer to avoid, like `MultiParamTypeClasses`. So we'll save the fun properties of `Sub` for later, when we define more specific sorts of substitutions.

Some other basic tools for working with `Sub`stitutions can be developed without this. First of all, over any grammar we have the empty substitution.

> emptySub :: Sub t
> emptySub = Sub M.empty

We'll also need a function that extracts the domain of a substitution -- the set of variables that get moved. We can think of a substitution as implicitly defined for _all_ variables, where the substitution acts like the identity for all but a finite number of them. Sometimes the set of "moved" inputs for a function like this is called its _support_.

> support :: Sub t -> S.Set (Var t)
> support (Sub m) = S.fromList $ M.keys m

Picky readers will notice that this is not really the support of a function in the strictest sense; it includes variables that get sent to expressions consisting only of themselves, and it's debatable whether this counts. Most of the time this doesn't matter to us, and when it does, we'll deal with it.

Here's a natural (if trivial) test: the support of an empty substitution should be the empty set.

> test_support_empty_sub
>   :: (Eq t) => Proxy t -> Bool
> test_support_empty_sub _ =
>   let empty = emptySub :: Sub t in
>   (support empty) == S.empty

We can also define an operator for building "singleton" substitutions whose support consists of only one variable. Normally I think it's bad form to use symbolic operators like this, but I'm making an exception here because this code is not intended to be a library for use in larger projects.

> (-->) :: Var t -> t -> Sub t
> x --> e = Sub $ M.fromList [(x,e)]

As a test, the support of $x \mapsto e$ is the singleton set $\{x\}$.

> test_support_singleton
>   :: (Eq t) => Proxy t -> Var t -> t -> Bool
> test_support_singleton _ x e =
>   (support (x --> e)) == S.singleton x

We'll also need a way to apply a substitution to a variable.

> applySub :: Var t -> Sub t -> Maybe t
> applySub x (Sub m) = M.lookup x m

Lookup should always fail on the empty substitution:

> test_sub_lookup_empty
>   :: (Eq t) => Proxy t -> Var t -> Bool
> test_sub_lookup_empty _ x =
>   Nothing == applySub x emptySub

We can precisely characterize what lookup does on singletons.

> test_sub_lookup_singleton
>   :: (Eq t) => Proxy t -> Var t -> Var t -> t -> Bool
> test_sub_lookup_singleton _ y x e =
>   if x == y
>     then Just e == applySub y (x --> e)
>     else Nothing == applySub y (x --> e)



Union
-----

We'll be interested in assembling substitutions into larger ones in a few different ways. As partial functions on the same domain, it makes sense to try to _union_ substitutions together. The problem with this is that in general the set union of two functions is not a function -- specifically, if they are both defined on some variable, but have different values there. So we'll need the union operator, `unionSub`, to return a `Maybe`.

> unionSub :: (Eq t) => Sub t -> Sub t -> Maybe (Sub t)
> unionSub (Sub m1) (Sub m2) = Sub <$> M.mergeA
>   (M.traverseMissing $ \_ x -> Just x)
>   (M.traverseMissing $ \_ x -> Just x)
>   (M.zipWithAMatched $ \_ x y -> if x == y then Just x else Nothing)
>   m1 m2

Here we've used the handy `mergeA` library function which can merge `Map`s using many different strategies. This makes it a little less clear what `unionSub` is doing, but we can check our intuition with some property tests.

Now `emptySub` should act like the empty set, `-->` should act like it constructs singletons, and `unionSub` should act like set union. Together these operators satisfy some intuitive properties.

The empty set acts like an identity with respect to union: $$\mathsf{unionSub}\ \mathsf{emptySub}\ s = s = \mathsf{unionSub}\ s\ \mathsf{emptySub}$$

> test_sub_union_identity
>   :: (Eq t) => Proxy t -> Sub t -> Bool
> test_sub_union_identity _ s = and
>   [ Just s == unionSub emptySub s
>   , Just s == unionSub s emptySub
>   ]

Union is idempotent: $$\mathsf{unionSub}\ s\ s = s$$

> test_sub_union_idempotent
>   :: (Eq t) => Proxy t -> Sub t -> Bool
> test_sub_union_idempotent _ s =
>   Just s == unionSub s s

Union is commutative: $$\mathsf{unionSub}\ s_1\ s_2 = \mathsf{unionSub}\ s_2\ s_1$$

> test_sub_union_commutative
>   :: (Eq t) => Proxy t -> Sub t -> Sub t -> Bool
> test_sub_union_commutative _ s1 s2 =
>   unionSub s1 s2 == unionSub s2 s1

Union is associative: $$\mathsf{unionSub}\ s_1\ (\mathsf{unionSub}\ s_2\ s_3) = \mathsf{unionSub}\ (\mathsf{unionSub}\ s_1\ s_2)\ s_3,$$ where if either side is undefined, then both are. (This test is a little more complicated because we have to deal with the `Maybe` result.)

> test_sub_union_associative
>   :: (Eq t) => Proxy t -> Sub t -> Sub t -> Sub t -> Bool
> test_sub_union_associative _ s1 s2 s3 =
>   let
>     lhs = do { t <- unionSub s1 s2; unionSub t s3 }
>     rhs = do { t <- unionSub s2 s3; unionSub s1 t }
>   in
>     lhs == rhs

We can characterize the union of singletons with the same support. If $e_1 \neq e_2$, then

$$\mathsf{unionSub}\ (x \mapsto e_1)\ (x \mapsto e_2) = \mathsf{Nothing}$$

> test_sub_union_nothing
>   :: (Eq t) => Proxy t -> Var t -> t -> t -> Bool
> test_sub_union_nothing _ x e1 e2 =
>   if e1 /= e2
>     then Nothing == (unionSub (x --> e1) (x --> e2))
>     else Just (x --> e1) == (unionSub (x --> e1) (x --> e2))

More generally, if a union is defined then the support of the (map) union is the (set) union of supports.

> test_sub_union_support
>   :: (Eq t) => Proxy t -> Sub t -> Sub t -> Bool
> test_sub_union_support _ s1 s2 =
>   case unionSub s1 s2 of
>     Nothing -> True
>     Just s3 -> support s3 == S.union (support s1) (support s3)

This last test is of lower quality than the others because the first case branch is trivial; our test suite will waste time generating test cases that provide no information. That's not to say the test is useless. If our implementation of `unionSub` _fails_ it's definitely wrong, but just because it _passes_ doesn't mean it's correct. This is true of all property tests, but especially so of those that essentially throw away test cases.



Extension
---------

Unioning substitutions is a partial operation because of what happens when two substitutions are defined but disagree on some input. Another way to deal with this problem is to simply declare that if $S_1$ and $S_2$ both substitute some variable $x$, just ignore what $S_2$ does and let the combination of $S_1$ and $S_2$ behave as if it were just $S_1$. We can think of this as a _left-biased_ union. Maybe a better way to think of it is that we are _augmenting_ $S_1$ with the additional values in $S_2$, ignoring any that conflict with what $S_1$ already does. This operation has the advantage of being total, at the expense of silently throwing away information.

> (.&) :: (Eq t) => Sub t -> Sub t -> Sub t
> (.&) (Sub m1) (Sub m2) = Sub $ M.union m1 m2

This implementation uses the fact that the `union` library function for `Map`s is left-biased.

Now for some properties. The empty substitution is again an identity with respect to extension: $$\mathsf{emptySub}\ \mathsf{.\&}\ s = s = s\ \mathsf{.\&}\ \mathsf{emptySub}$$

> test_sub_extend_empty
>   :: (Eq t) => Proxy t -> Sub t -> Bool
> test_sub_extend_empty _ s = and
>   [ s == (emptySub .& s)
>   , s == (s .& emptySub)
>   ]

Extension is idempotent: $$s\ \mathsf{.\&}\ s = s$$

> test_sub_extend_idempotent
>   :: (Eq t) => Proxy t -> Sub t -> Bool
> test_sub_extend_idempotent _ s =
>   s == (s .& s)

Extension on singletons with the same variable is a left-zero operation: $$(x \mapsto e_1)\ \mathsf{.\&}\ (x \mapsto e_2) = (x \mapsto e_1)$$

> test_sub_extend_singleton
>   :: (Eq t) => Proxy t -> Var t -> t -> t -> Bool
> test_sub_extend_singleton _ x e1 e2 =
>   (x --> e1) == (x --> e1) .& (x --> e2)

And extension is associative: $$s_1\ \mathsf{.\&}\ (s_2\ \mathsf{.\&}\ s_3) = (s_1\ \mathsf{.\&}\ s_2)\ \mathsf{.\&}\ s_3$$

> test_sub_extend_associative
>   :: (Eq t) => Proxy t -> Sub t -> Sub t -> Sub t -> Bool
> test_sub_extend_associative _ s1 s2 s3 =
>   s1 .& (s2 .& s3) == (s1 .& s2) .& s3

Finally, the support of an extension is the union of supports. Compare this to the analogous property for `unionSub`.

> test_sub_extend_support
>   :: (Eq t) => Proxy t -> Sub t -> Sub t -> Bool
> test_sub_extend_support _ s1 s2 =
>   support (s1 .& s2) == S.union (support s1) (support s2)



Restriction
-----------

One more operation on substitutions will come in handy: _restriction_. This will "undefine" a substitution on some set of variables; it's sort of the inverse of extension.

> (</) :: Sub t -> S.Set (Var t) -> Sub t
> (Sub s) </ as =
>   Sub $ M.difference s (M.fromSet (const ()) as)

The signature for `</` is that of a right action -- in this case, the set of sets of variables over `t` acting on the set of substitutions over `t`. The type `S.Set (Var t)` has some structure of its own; in particular, it's a monoid under (set) union. A natural question is then whether `</` is a _monoid_ action -- and indeed it is.

Remember that a _monoid_ is a set $M$ with an associative binary operation $\cdot$ and an identity element $e$; that is, for all $a$, $b$, and $c$ in $M$ we have $a \cdot (b \cdot c) = (a \cdot b) \cdot c$ and $a \cdot e = a = e \cdot a$. If we have another operation $\ast$ with signature $A \times M \rightarrow A$, then this is a _monoid action_ of $M$ on $A$ if we have $u \ast e = u$ and $(u \ast a) \ast b = u \ast (a \cdot b)$ for all $u \in A$ and $a,b \in M$. These properties are very special, and easy to test for.

> test_undefine_identity
>   :: (Eq t) => Proxy t -> Sub t -> Bool
> test_undefine_identity _ s =
>   s == (s </ S.empty)
> 
> test_undefine_action
>   :: (Eq t)
>   => Proxy t -> Sub t -> S.Set (Var t) -> S.Set (Var t) -> Bool
> test_undefine_action _ s as bs =
>   ((s </ as) </ bs) == (s </ (as <> bs))

This is just the first of several monoid actions we'll see.

Finally, we can characterize undefine on a singleton substitution.

> test_undefine_singleton
>   :: (Eq t) => Proxy t -> Var t -> t -> Bool
> test_undefine_singleton _ x e =
>   emptySub == (x --> e) </ (S.singleton x)

In the next section we'll develop the grammar of lambda calculus with let bindings.
