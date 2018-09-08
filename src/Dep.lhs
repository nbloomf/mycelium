---
title: Dependencies
---

> {-# LANGUAGE LambdaCase #-}
> module Dep where

> import Data.GraphViz.Algorithms
> import Data.GraphViz.Attributes
> import Data.GraphViz.Types
> import Data.GraphViz.Types.Graph (mkGraph)
> import Data.GraphViz.Types.Canonical
> import Data.GraphViz.Commands.IO
> import Data.GraphViz.Printing
> import Data.Maybe (catMaybes)

> import Proof
> import Module

> data Dep
>   = DepInferenceRule RuleName
>   | DepDefinition RuleName
>   | DepTheorem RuleName [RuleName]

> proofDeps :: Proof -> [RuleName]
> proofDeps = \case
>   Use _ n _ p -> n : concatMap proofDeps p
>   Hyp _ _ _ -> []
>   Dis _ _ _ _ -> []
>   ElimEq _ _ _ _ p1 p2 ->
>     (RuleName "eq-elim") : concatMap proofDeps [p1,p2]
>   IntroEq _ _ -> [RuleName "eq-intro"]
>   IntroU _ _ _ _ p ->
>     (RuleName "forall-intro") : proofDeps p
>   ElimU _ _ _ _ p ->
>     (RuleName "forall-elim") : proofDeps p
>   IntroE _ _ _ _ p ->
>     (RuleName "exists-intro") : proofDeps p
>   ElimE _ _ _ _ p1 p2 ->
>     (RuleName "exists-elim") : concatMap proofDeps [p1,p2]
>   Subst _ _ _ p -> proofDeps p
>   Assume _ _ _ -> []

> toDep :: Claim -> Maybe Dep
> toDep = \case
>   Axiom t n _ -> Just $ case t of
>     InferenceRule -> DepInferenceRule n
>     Definition -> DepDefinition n
>   Theorem n _ p -> Just $
>     DepTheorem n $ proofDeps p
>   TypeDecl _ _ -> Nothing

> getDeps :: [Claim] -> [Dep]
> getDeps = catMaybes . map toDep

> getAllDeps :: [Module] -> [Dep]
> getAllDeps = concatMap (\(Module _ cs) -> getDeps cs)

> summarizeDeps :: [Dep] -> (Int, Int, Int)
> summarizeDeps = foldr (\(a1,b1,c1) (a2,b2,c2) -> (a1+a2,b1+b2,c1+c2)) (0,0,0) . map f
>   where
>     f = \case
>       DepInferenceRule _ -> (1,0,0)
>       DepDefinition _ -> (0,1,0)
>       DepTheorem _ _ -> (0,0,1)

> instance PrintDot RuleName where
>   unqtDot (RuleName n) = unqtDot n
>   toDot (RuleName n) = toDot n

> fromDepToGraph :: Dep -> ([DotNode RuleName], [DotEdge RuleName])
> fromDepToGraph = \case
>   DepInferenceRule n -> ([DotNode n [color Green]], [])
>   DepDefinition n -> ([DotNode n [color Blue]], [])
>   DepTheorem n ms -> ([DotNode n [shape BoxShape]], map (\m -> DotEdge m n []) ms)

> fromDepsToGraph :: [Dep] -> DotGraph RuleName
> fromDepsToGraph ds =
>   transitiveReduction $ canonicalise $ uncurry mkGraph $ mconcat $ map fromDepToGraph ds

> printDot :: FilePath -> [Dep] -> IO ()
> printDot path ds = writeDotFile path (fromDepsToGraph ds)
