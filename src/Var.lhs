---
title: Variables and Constants
---

In this program we'll be working with a few different _grammars_. Most formal grammars are built using at least two basic parts: _variables_ and _constants_. Constants represent "concrete" entities that stand for themselves, while variables represent "abstract" entities that can stand for something else. The most important difference between the two is that it makes sense to "substitute" an expression for a variable, but not for a constant.

We'll be working with a handful of grammars that differ slightly in the details, but most will use variables and constants. In this module we define some helpers for working with these in a type-safe way.

We start with some module imports.

> {-# LANGUAGE ScopedTypeVariables #-}
> module Var where
>
> import Data.Proxy
>   ( Proxy(Proxy) )
> import qualified Data.Set as S
>   ( Set(..), notMember )
> import Test.QuickCheck
>   ( Property )



Constants and Variables
-----------------------

The most important features of both constants and variables are that

1. Given two constants (or variables), we can tell whether they are "the same" or "different", and
2. We have an inexhaustable supply of new ones -- given any set of constants (or variables), it's possible to construct another that is "different" from the ones we start with.

Another property we'll need later is

3. Given two different constants (or variables) we can effectively determine that one of them is "smaller" than the other.

`String`s can do that; we can compare them for equality, sort them lexicographically, and always generate new ones.

> data Con t = Con String
>   deriving (Eq, Ord, Show)
> 
> data Var t = Var String
>   deriving (Eq, Ord, Show)

Both of these types are essentially strings, but note that extra phantom type parameter `t`. Since `t` doesn't appear on the right hand side of the definition it vanishes at runtime. But that parameter makes it possible to distinguish among different _sorts_ of constants and variables. When we're dealing with multiple grammars this will make it harder to mix different sorts by mistake.

Although `Con` and `Var` have essentially identical definitions, they will be treated very differently.



Freshness
---------

An important operation on both variables and constants is that of constructing _fresh_ ones. Given a set of variables, we should always be able to construct another that doesn't belong to the set. We'll abstract this behind a type class, and for efficiency, will allow a _list_ of sets of variables to avoid, rather than just one set.

> class Fresh a where
>   fresh :: [S.Set a] -> a

We can to define `Fresh` instances for both `Var` and `Con`.

> instance Fresh (Var t) where
>   fresh olds = head $ filter new vars
>     where
>       new :: Var t -> Bool
>       new x = all (S.notMember x) olds
> 
>       -- an infinite supply
>       vars :: [Var t]
>       vars = [ Var $ 'x' : show i | i <- [0..] ]
> 
> instance Fresh (Con t) where
>   fresh olds = head $ filter new cons
>     where
>       new :: Con t -> Bool
>       new x = all (S.notMember x) olds
> 
>       -- an infinite supply
>       cons :: [Con t]
>       cons = [ Con $ 'c' : show i | i <- [0..] ]

All the best type classes have *laws* -- that is, universally quantified properties we expect them to satisfy. Typeclass laws are great because they serve as checks on our intuition and make natural property tests. In the case of `fresh`, the most important property is that `fresh s` is not an element of `s`. We can make this a property test like so.

> test_fresh_not_member
>   :: (Fresh a, Ord a)
>   => Proxy a -> [S.Set a] -> Bool
> 
> test_fresh_not_member _ olds =
>   all (S.notMember $ fresh olds) olds

(Note the `Proxy` argument. This is a safe and easy way to let callers of this test fix the `a` type parameter, which would otherwise be ambiguous.)

This test takes a list of sets of `a`s, generates a fresh `a`, and verifies that the fresh `a` is not a member of any of the input sets. So one way to test our `fresh` implementations is to generate random `[S.Set a]`s and hammer them with this test -- it should always evaluate to `True`. We can use the `QuickCheck` testing library to do exactly this. In case you haven't seen it before, this idea is called _property based_ or _generative_ testing, and it can be devastatingly effective at finding bugs. We will use it often.
