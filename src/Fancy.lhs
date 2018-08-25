---
title: Fancy Proofs
---

A natural deduction proof is a tree. In practice, reading and writing proof trees has some drawbacks. When proofs reach a certain size it can be difficult to lay out a tree-formatted proof on the page. Also, trees aren't a great fit for the way we usually read text from beginning to end.

There's an alternative syntax for natural deduction, which is basically a depth-first serialization of the proof tree. For instance, the tree

```
* A
  * B
    * C
  * D
    * E
      * F
    * G
```

might be serialized as

```
1. C;
2. B; 1
3. F;
4. E; 3
5. G;
6. D; 4, 5
7. A; 2, 6
```

In other words, write the nodes of the tree as a numbered list, where each node is accompanied by a list of references to its children. There are many valid ways to serialize a tree, but a valid serialization represents a unique tree.

This is almost [Fitch notation](https://en.wikipedia.org/wiki/Fitch_notation), with one exception -- because a serialized proof represents a unique tree, it isn't necessary to use indentation to signify what hypotheses have been introduced but not discharged. (It's a good idea to do this anyway for human readers, but the proof checker doesn't need it.)

The serialized syntax has some advantages. It doesn't require arbitrary indentation -- which is a big problem for large proofs. It is more natural to read from top to bottom. And it facilitates writing shorter proofs when a subproof appears more than once, although this is not very common.

In this module we'll define an alternative abstract syntax for serialized proofs, which we'll call _fancy style_.

As usual we start with imports.

> {-# LANGUAGE LambdaCase #-}
> module Fancy where
> 
> import Data.List
> import qualified Data.Map as M
> import Test.QuickCheck
> 
> import Var
> import Sub
> import Expr
> import Jud
> import Proof



The Representation
------------------

Where a proof is a tree of proofs, a fancy proof is a list of proof statements.

Fancy proof statements will look suspiciously like the nodes in a nonfancy proof, except that _subproofs_ will be replaced by _references_. The lines in a fancy proof are usually numbered, so the references can just be `Int`s.

> data FancyProof
>   = FancyProof (M.Map Int FancyProofLine)
>   deriving (Eq, Show)
> 
> data FancyProofLine
>   = FancyUse Loc RuleName Jud [Int]
>   | FancyHyp Loc HypName Jud
>   | FancyDis Loc HypName Jud Int
>   | FancyElimEq Loc Jud (Var Expr) Jud Int Int
>   | FancyIntroU Loc Jud (Var Expr) (Var Expr) Int
>   | FancyElimU Loc Jud (Var Expr) Expr Int
>   | FancySubst Loc Jud (Sub Expr) Int
>   | FancyAssume Loc Int Jud
>   deriving (Show)

For testing we'll need an `Eq` instance for `FancyProofLine` that ignores the `Loc` parameters.

> instance Eq FancyProofLine where
>   l1 == l2 = case (l1,l2) of
>     (FancyUse _ n1 q1 ps1, FancyUse _ n2 q2 ps2) ->
>       (n1 == n2) && (q1 == q2) && (ps1 == ps2)
>     (FancyHyp _ n1 q1, FancyHyp _ n2 q2) ->
>       (n1 == n2) && (q1 == q2)
>     (FancyDis _ n1 q1 p1, FancyDis _ n2 q2 p2) ->
>       (n1 == n2) && (q1 == q2) && (p1 == p2)
>     (FancyElimEq _ q1 x1 w1 u1 v1, FancyElimEq _ q2 x2 w2 u2 v2) ->
>       (q1 == q2) && (x1 == x2) && (w1 == w1) && (u1 == u2) && (v1 == v2)
>     (FancyIntroU _ q1 x1 y1 p1, FancyIntroU _ q2 x2 y2 p2) ->
>       (q1 == q2) && (x1 == x2) && (y1 == y2) && (p1 == p2)
>     (FancyElimU _ q1 x1 e1 p1, FancyElimU _ q2 x2 e2 p2) ->
>       (q1 == q2) && (x1 == x2) && (e1 == e2) && (p1 == p2)
>     (FancySubst _ q1 s1 p1, FancySubst _ q2 s2 p2) ->
>       (q1 == q2) && (s1 == s2) && (p1 == p2)
>     (FancyAssume _ n1 q1, FancyAssume _ n2 q2) ->
>       (n1 == n2) && (q1 == q2)
>     _ -> False

For funsies, here's an `Arbitrary` instance.

> instance Arbitrary FancyProofLine where
>   arbitrary = oneof
>     [ FancyUse <$> arbitrary <*> arbitrary <*> arbitrary
>         <*> ((map abs) <$> arbitrary)
>     , FancyHyp <$> arbitrary <*> arbitrary <*> arbitrary
>     , FancyDis <$> arbitrary <*> arbitrary <*> arbitrary
>         <*> (abs <$> arbitrary)
>     , FancyElimEq <$> arbitrary <*> arbitrary <*> arbitrary
>         <*> arbitrary <*> (abs <$> arbitrary) <*> (abs <$> arbitrary)
>     , FancyIntroU <$> arbitrary <*> arbitrary <*> arbitrary
>         <*> arbitrary <*> (abs <$> arbitrary)
>     , FancyElimU <$> arbitrary <*> arbitrary <*> arbitrary
>         <*> arbitrary <*> (abs <$> arbitrary)
>     , FancySubst <$> arbitrary <*> arbitrary <*> arbitrary
>         <*> (abs <$> arbitrary)
>     , FancyAssume <$> arbitrary <*> (abs <$> arbitrary) <*> arbitrary
>     ]
> 
>   shrink = \case
>     FancyUse loc name q ps ->
>       [ FancyUse loc name q' ps | q' <- shrink q ]
>     FancyHyp loc name q ->
>       [ FancyHyp loc name q' | q' <- shrink q ]
>     FancyDis loc name q p ->
>       [ FancyDis loc name q' p | q' <- shrink q ]
>     FancyElimEq loc q x w pe pf ->
>       [ FancyElimEq loc q' x w' pe pf |
>           q' <- shrink q, w' <- shrink w ] ++
>       [ FancyElimEq loc q x w' pe pf | w' <- shrink w ] ++
>       [ FancyElimEq loc q' x w pe pf | q' <- shrink q ]
>     FancyIntroU loc q x y p ->
>       [ FancyIntroU loc q' x y p | q' <- shrink q ]
>     FancyElimU loc q x e p ->
>       [ FancyElimU loc q' x e' p | q' <- shrink q, e' <- shrink e ] ++
>       [ FancyElimU loc q' x e p | q' <- shrink q ] ++
>       [ FancyElimU loc q x e' p | e' <- shrink e ]
>     FancySubst loc q s p ->
>       [ FancySubst loc q' s' p | q' <- shrink q, s' <- shrink s ] ++
>       [ FancySubst loc q' s p | q' <- shrink q ] ++
>       [ FancySubst loc q s' p | s' <- shrink s ]
>     FancyAssume loc t q ->
>       [ FancyAssume loc t q' | q' <- shrink q ]
> 
> instance Arbitrary FancyProof where
>   arbitrary = do
>     m <- M.mapKeys abs <$> arbitrary
>     k <- abs <$> arbitrary
>     a <- arbitrary
>     return $ FancyProof $ M.insert k a m
> 
>   shrink (FancyProof m) = map FancyProof $ shrink m

We will not directly validate fancy proofs -- instead we will convert them to their canonical nonfancy form and validate that. The fancy form is just an alternative abstract (and later, concrete) syntax.

Deserialization of a fancy proof can fail in a few ways; we might have a reference to a nonexistent proof step. We might have a reference from an early step to a later step; to ensure that deserialization terminates this should not be allowed. Also we will demand that the step labels be natural numbers.

> data DeserializeError
>   = StepNotPresent Int
>   | NegativeRef Int
>   | ForwardRef Int Int
>   | EmptyProof
>   deriving (Eq, Show)

To deserialize, we construct the tree proof from the leaves to the root.

> deserialize :: FancyProof -> Either DeserializeError Proof
> deserialize (FancyProof m) = case M.lookupMax m of
>   Nothing -> Left EmptyProof
>   Just (t,_) -> deserializeAt t
>   where
>     deserializeAt k = if k < 0
>       then Left $ NegativeRef k
>       else case M.lookup k m of
>         Nothing -> Left $ StepNotPresent k
>         Just t -> case t of
>           FancyHyp loc name q -> Right $ Hyp loc name q
>           FancyDis loc name q u -> do
>             p <- deserializeBelowAt k u
>             return $ Dis loc name q p
>           FancyElimEq loc q x e u v -> do
>             pu <- deserializeBelowAt k u
>             pv <- deserializeBelowAt k v
>             return $ ElimEq loc q x e pu pv
>           FancyIntroU loc q x y u -> do
>             p <- deserializeBelowAt k u
>             return $ IntroU loc q x y p
>           FancyElimU loc q x e u -> do
>             p <- deserializeBelowAt k u
>             return $ ElimU loc q x e p
>           FancySubst loc q s u -> do
>             p <- deserializeBelowAt k u
>             return $ Subst loc q s p
>           FancyAssume loc t q -> Right $ Assume loc t q
>           FancyUse loc name q us -> do
>             ps <- mapM (deserializeBelowAt k) us
>             return $ Use loc name q ps
> 
>     deserializeBelowAt k u =
>       if u >= k
>         then Left $ ForwardRef u k
>         else do
>           p <- deserializeAt u
>           return p



Serialization
-------------

In practice there isn't really a good reason to turn a nonfancy proof into a fancy proof, since the most important thing we do with proofs is validate them.

But a good test of our deserialization function is that deserializing a serialized nonfancy proof should be the identity. In the spirit of overdoing it, lets write that test.

In the following code, we'll be implicitly assuming that the lines of a proof are numbered contiguously from 1 to $n$. This won't be checked, since this is just test code which should break if that invariant is not satisfied. This constraint is not necessary when we actually use the library, but makes the test much simpler.

We need a couple of utilities. First is `catFancyProof`, which concatenates two fancy proofs and updates the line labels in the second.

> catFancyProof :: FancyProof -> FancyProof -> FancyProof
> catFancyProof p@(FancyProof m1) (FancyProof m2) =
>   let k = sizeOf p in
>   FancyProof $ M.union m1 (fmap (bump k) $ M.mapKeys (k+) m2)
>   where
>     bump :: Int -> FancyProofLine -> FancyProofLine
>     bump k = \case
>       FancyUse loc name q ps -> FancyUse loc name q (map (k+) ps)
>       FancyHyp loc name q -> FancyHyp loc name q
>       FancyDis loc name q p -> FancyDis loc name q (k+p)
>       FancyElimEq loc q x w u v -> FancyElimEq loc q x w (k+u) (k+v)
>       FancyIntroU loc q x y p -> FancyIntroU loc q x y (k+p)
>       FancyElimU loc q x e p -> FancyElimU loc q x e (k+p)
>       FancySubst loc q s p -> FancySubst loc q s (k+p)
>       FancyAssume loc t q -> FancyAssume loc t q

We also need `sizeOf`, which gets the largest line label of a fancy proof. 

> sizeOf :: FancyProof -> Int
> sizeOf (FancyProof m) = case M.lookupMax m of
>   Nothing -> 0
>   Just (k,_) -> k

We're now prepared to serialize proofs. The result is a _list_ of fancy proofs, because there's generally more than one way to serialize a proof. We don't enumerate all of them for simplicity's sake.

> serialize :: Proof -> [FancyProof]
> serialize = \case
>   Assume loc k p ->
>     [ FancyProof $ M.fromList [ (1, FancyAssume loc k p) ] ]
>   Hyp loc name p ->
>     [ FancyProof $ M.fromList [ (1, FancyHyp loc name p) ] ]
>   Dis loc name q p -> do
>     m <- serialize p
>     let k = sizeOf m
>     [ append m $ FancyProof $ M.fromList
>       [ (1, FancyDis loc name q k) ] ]
>   ElimEq loc w x q pe pf -> do
>     me <- serialize pe
>     mf <- serialize pf
>     let ke = sizeOf me
>     let kf = sizeOf mf
>     [   append (catFancyProof me mf) $ FancyProof $ M.fromList
>         [ (1, FancyElimEq loc w x q ke (ke+kf)) ]
>       , append (catFancyProof mf me) $ FancyProof $ M.fromList
>         [ (1, FancyElimEq loc w x q (ke+kf) kf) ]
>       ]
>   Subst loc q s p -> do
>     m <- serialize p
>     let k = sizeOf m
>     [ append m $ FancyProof $ M.fromList
>       [ (1, FancySubst loc q s k) ] ]
>   IntroU loc w x y p -> do
>     m <- serialize p
>     let k = sizeOf m
>     [ append m $ FancyProof $ M.fromList
>       [ (1, FancyIntroU loc w x y k) ] ]
>   ElimU loc w x e p -> do
>     m <- serialize p
>     let k = sizeOf m
>     [ append m $ FancyProof $ M.fromList
>       [ (1, FancyElimU loc w x e k) ] ]
>   Use loc name q ps -> do
>     ms <- mapM serialize ps
>     let ks = map sizeOf ms
>     let accum = map sum . tail . inits
>     [ append
>       (foldr catFancyProof (FancyProof mempty) ms)
>         (FancyProof $ M.fromList
>           [ (1, FancyUse loc name q (accum ks)) ]) ]
> 
>   where
>     append p@(FancyProof m1) (FancyProof m2) =
>       let k = sizeOf p in
>       FancyProof $ M.union m1 (M.mapKeys (k+) m2)

And we can test that deserializing a serialized proof returns the same proof. Going in the other direction is less straightforward, since fancy proofs are subject to syntactic validation.

> test_deserialize :: Proof -> Bool
> test_deserialize p =
>   and [ Right p == deserialize q | q <- serialize p ]
