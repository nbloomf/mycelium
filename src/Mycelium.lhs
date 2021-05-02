---
title: Mycelium
---

Introduction
------------

This document is the annotated Haskell source code for `mycelium`, a tool for mechanically checking natural deduction style proofs whose terms are simply typed lambda calculus expressions with let bindings. Mycelium is meant to be simple and small but also practical for writing proofs.

None of the ideas here are new or even very complicated; natural deduction has been widely studied since its introduction by Jaśkowski in the 1920s, lambda calculus was first described by Church in the 1930s, and the Damas-Hindley-Milner type inference algorithm dates to the 1970s. `mycelium` is sort of an experiment to see how far these old, simple ideas can take us.

Proof checking is a good fit for the Haskell language and the literate programming style for a few reasons. Proofs are essentially expressions built using a handful of different _grammars_, which are nicely modeled using algebraic data types. Most of the tests we might write to check our implementation can be expressed as algebraic properties, rather than one off or ad-hoc tests, making them amenable to generative testing. And we can develop the program from the bottom up with essentially linear dependencies; this document can be read from beginning to end without forward references.

We begin by developing the abstract syntax of proofs, which can be divided into four grammars: one for _lambda expressions_, one for _types_, one for _judgements_ and one for _proofs_. This is the bulk of the code. After establishing this abstract syntax we move to the _concrete syntax_, enabling ourselves to parse a (more) succinct textual representation of proofs. Finally, we package these tools into a command line program for unix-like environments.



Contents
--------

* Abstract Syntax
  * Lambda Expressions
    * [Variables and Constants](./Var.html)
    * [Substitutions](./Sub.html)
    * [Expressions](./Expr.html)
  * Types and Type Inference
    * [Types](./Type.html)
    * [Inference](./Infer.html)
  * Judgement and Proof
    * [Judgements](./Jud.html)
    * [Proofs](./Proof.html)
* Concrete Syntax
  * [Modules](./Module.html)
  * [Fancy Proofs](./Fancy.html)
  * [Parsing](./Parser.html)
* Appendices
  * [Main](./Main.html)
  * [Tests](./Tests.html)
  * [Dependency Visualization](./Dep.html)



Pragmatics
----------

This file is the base module of a Haskell library which implements the `mycelium` grammar and parser; all it does is reexport the rest of the library.

> module Mycelium (
>     module Var
>   , module Sub
>   , module Expr
>   , module Type
>   , module Infer
>   , module Jud
>   , module Proof
>   , module Module
>   , module Fancy
>   , module Parser
>   , module Dep
> ) where
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
> import Dep



Acknowledgements
----------------

Portions of the HM implementation code are adapted from David Luposchainsky's [tutorial](https://github.com/quchen/articles/tree/master/hindley-milner), which really helped me understand what was going on as I read [Damas' thesis](http://prl.ccs.neu.edu/img/d-thesis-1984.pdf) and [Damas and Milner's paper](https://web.cs.wpi.edu/~cs4536/c12/milner-damas_principal_types.pdf) on type inference.
