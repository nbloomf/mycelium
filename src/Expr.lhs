---
title: Expressions
---

In this section we'll define a grammar of _expressions_. This grammar will just be [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus) with an additional syntactic form, called a _let binding_, which is semantically redundant but practically useful.

A natural question we should be asking is, _why lambda calculus_? There are a few reasons.

1. It is simple. As a grammar it has only five production rules.
2. It is powerful. In principle any reasonable model of computation can be translated to LC; it's also the basis of practical Lisp-family and ML-family languages.
3. It is familiar. Lambda calculus is the OG modern computational formalism, it's been in use for over 80 years, and the syntax is essentially function notation from mathematics.
4. It has an efficient [_type inference algorithm_](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system), to be discussed later.

Lambda calculus hits a sweet spot on the simplicity/power spectrum. It is _boring_ in the best sense of the word; it is old and very well understood.

As usual, we start with some module imports.

> {-# LANGUAGE LambdaCase, FlexibleInstances, BangPatterns #-}
> module Expr where
> 
> import qualified Data.Map as M
>   ( Map, fromList, toList, elems )
> import Data.Proxy
>   ( Proxy(Proxy) )
> import qualified Data.Set as S
>   ( Set, insert, member, disjoint, empty, singleton
>   , unions, notMember, fromList, union, delete )
> import Test.QuickCheck
>   ( Arbitrary(..), Gen, elements, oneof, getSize )
> 
> import Var
> import Sub



Lambda Calculus
---------------

Recall that _lambda expressions_ are built up inductively using the following rules:

* **Var**: Every variable is a lambda expression.
* **Lam**: If $x$ is a variable and $e$ is a lambda expression, then $\lambda x . e$ is a lambda expression. The $x$ here is a dummy variable; it's precise name is not significant.
* **App**: If $e_1$ and $e_2$ are lambda expressions, then $e_1 e_2$ is a lambda expression.
* **Par**: If $e$ is a lambda expression, then $(e)$ is a lambda expression.

We will augment this with two additional rules:

* **Con**: Every constant is a lambda expression.
* **Let**: If $x$ is a variable and $e_1$ and $e_2$ are lambda expressions, then $\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2$ is a lambda expression. The $x$ here is also a dummy variable.

The Con rule effectively defines a new class of variable, all of whose members are automatically bound "outside the expression".

The Let rule can be interpreted in terms of App and Lam; the expression $\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2$ will end up being equivalent to $(\lambda x . e_2)e_1$. Later we will be inferring types for expressions, and it turns out there are some typeable expressions involving let whose lambda forms are not typeable; this reasonably minor syntactic extension makes our type system more powerful.

Anyway, here's a Haskell type representing the production rules for expressions. The parentheses rule is implicit, and only really needed when expressions are serialized as strings. This type has one extra complication: the `Loc` parameter, which will eventually represent a _source location_ so we can report useful error messages, but for now is not important.

> data Expr
>   = ECon Loc (Con Expr)
>   | EVar Loc (Var Expr)
>   | ELam Loc (Var Expr) Expr
>   | ELet Loc (Var Expr) Expr Expr
>   | EApp Loc Expr Expr
>   deriving (Show)
> 
> data Loc
>   = Q -- "Nowhere"
>   | Loc String Int Int
>   deriving (Eq, Ord, Show)

We also need an `Arbitrary` instance for generating `Expr`s. This generator uses an explicit depth parameter, based on `QuickCheck`'s _size_ state, to ensure that each recursive step generates a smaller `Expr`. An earlier version of this generator simply chose one of `Expr`s constructors to generate, which led to comically large test cases.

> instance Arbitrary Expr where
>   arbitrary = getSize >>= genDepth
>     where
>       genDepth :: Int -> Gen Expr
>       genDepth k
>         | k <= 0 = oneof
>             [ ECon <$> arbitrary <*> arbitrary
>             , EVar <$> arbitrary <*> arbitrary
>             ]
>         | otherwise = do
>             let recur = genDepth =<< elements [0..(k-1)]
>             oneof
>               [ ELam <$> arbitrary <*> arbitrary <*> recur
>               , ELet <$> arbitrary <*> arbitrary <*> recur <*> recur
>               , EApp <$> arbitrary <*> recur <*> recur
>               ]
> 
>   shrink = \case
>     ECon _ _ -> []
>     EVar _ _ -> []
>     ELam loc x e -> (e:) $ map (ELam loc x) $ shrink e
>     ELet loc x e1 e2 ->
>       [ e1, e2 ] ++
>       [ ELet loc x f1 f2 | f1 <- shrink e1, f2 <- shrink e2 ] ++
>       [ ELet loc x e1 f2 | f2 <- shrink e2 ] ++
>       [ ELet loc x f1 e2 | f1 <- shrink e1 ]
>     EApp loc e1 e2 ->
>       [ e1, e2 ] ++
>       [ EApp loc f1 f2 | f1 <- shrink e1, f2 <- shrink e2 ] ++
>       [ EApp loc e1 f2 | f2 <- shrink e2 ] ++
>       [ EApp loc f1 e2 | f1 <- shrink e1 ]
> 
> instance Arbitrary Loc where
>   arbitrary = Loc <$> arbitrary <*> arbitrary <*> arbitrary

We also define an `Arbitrary` instance for `Con Expr`s and `Var Expr`s. For simplicity this instance generates constants of the form `cN` and variables of the form `xN` where `N` is a natural number.

> instance Arbitrary (Var Expr) where
>   arbitrary = do
>     k <- getSize
>     i <- elements [0..k]
>     return $ Var $ 'x' : show i
> 
> instance Arbitrary (Con Expr) where
>   arbitrary = do
>     k <- getSize
>     i <- elements [0..k]
>     return $ Con $ 'c' : show i

Note how the distribution of `N`s depends on `QuickCheck`s implicit _size_ parameter. The idea is that larger sizes result in a larger pool of symbols to draw from. This dynamic behavior is useful because small and large variable pools will tax our property tests in different ways.



Alpha Equivalence
-----------------

Note that we haven't derived an `Eq` instance for `Expr`. This is because the derived _syntactic_ equality on `Expr` is too strict. It would consider the expressions $\lambda x . x$ and $\lambda y . y$ to be different, even though they only differ in their dummy variables. We'll be introducing transformations on `Expr`s that may change the names of dummy variables, and need our notion of equality to account for this -- we need to compare expressions for equality "up to a renaming of the dummy variables". This expanded notion of equality is known as _alpha equivalence_.

In order to do this correctly, we need a better understanding of exactly what a dummy variable is.

Every syntactic occurrence of a variable in an `Expr` can be characterized as either _bound_, _free_, or a _binding site_. For example, in $\lambda x . e$, we say that $x$ is a _binding site_, and any occurrences of $x$ in $e$ are _bound_. However! The occurrences of $x$ in $e$ are not necessarily bound at this binding site. If some subexpression of $e$ is of the form $\lambda x . f$, then any occurrences of $x$ in $f$ (which, mind, are also occurrences of $x$ in $e$) are bound _there_, unless of course $f$ has a subexpression with an $x$ binding site... to distinguish $x$s that are bound at the outer $\lambda$ from those bound in the inner $\lambda$s we need to distinguish between _free_ (not bound) occurrences of $x$ in $e$ (not in $\lambda x.e$) and _bound_ occurrences of $x$ in $e$. This is confusing!

The characterization of variable occurrences in this way is _very fragile_ and fiddly; I think it's helpful to nail down our ideas in code. To this end, let's start with a function that finds all of the free variables in an expression; these are the variables that are not bound in a lambda or let expression.

> freeExprVarsE :: Expr -> S.Set (Var Expr)
> freeExprVarsE x = case x of
>   ECon !loc _ ->
>     S.empty

Constant expressions have no free variables. That seems pretty clear.

>   EVar !loc x ->
>     S.singleton x

Variable expressions have one free variable. That also seems pretty clear; this variable isn't bound by either a lambda or a let. But wait! What if this is a subexpression of some larger expression where the variable _is_ bound? We don't have to worry about that. Remember that the characterization of variables as bound or free depends intimately on exactly what expression we're talking about, and here we have just a variable. Lambda and let expressions will have to fend for themselves.

>   ELam !loc x e ->
>     S.delete x $ freeExprVarsE e

Lambda expressions! In $\lambda x . e$, it seems clear that any variables that are free _in_ $e$ will remain free in $\lambda x . e$, with one exception: any free occurrences of $x$ in $e$ become bound in $\lambda x . e$.

>   ELet !loc x e1 e2 ->
>     S.union (freeExprVarsE e1) (S.delete x $ freeExprVarsE e2)

Let expressions are the other place where a variable can be bound. Remember that $\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2$ should behave like $(\lambda x . e_2)e_1$. Certainly any variables _except_ $x$ that appear in either $e_1$ or $e_2$ should remain free in the let. And certainly any $x$s appearing in $e_2$ become bound in the let; this is consistent with the way free variables work in lambda expressions. But what about $x$s that appear free in $e_1$? Note that they do not become bound in the let -- let bindings are not recursive. Some languages that use let bindings in this way provide an additional form, like "letrec", that does bind recursively. We're intentionally not doing this because it complicates type inference.

>   EApp !loc e1 e2 ->
>     S.union (freeExprVarsE e1) (freeExprVarsE e2)

Finally, the application rule does not bind any variables, so the set of free variables is the union of the sets of free variables of the constituent expressions.

We can check that `freeExprVars` behaves as expected with some test cases.

> test_cases_freeExprVars :: Bool
> test_cases_freeExprVars = and
>   [ (==)
>       (freeExprVarsE
>         (ELam Q (Var "x")
>           (EApp Q (EVar Q (Var "y")) (EVar Q (Var "x")))))
>       (S.fromList [Var "y"])
> 
>   , (==)
>       (freeExprVarsE
>         (ELet Q (Var "x") (EVar Q (Var "y"))
>           (EVar Q (Var "z"))))
>       (S.fromList [Var "y", Var "z"])
>   ]

Reasonable enough, although typing out all those `Expr`s is a pain. (Eventually we'll define a more compact syntax for this, but for now working with the raw representation is good enough.)

A useful operation on expressions is to _rename_ the variables. Normally we don't want to do this for "top level" expressions, because while bound variables can in principle be renamed without changing the expression, free variables cannot. However, renaming free occurrences will turn out to be a useful stepping stone to detecting when two expressions are alpha equivalent. We will need two different kinds of renamings: of free and bound variables. The signatures of these will be a little different. When renaming a free variable we will usually have a specific replacement name in mind, but when renaming bound variables we won't really care what the new name is, but will have a set of variable names to _avoid_.

The renaming functions for `Expr` are delicate, so we'll define them one at a time with tests between.

`renameFreeE (u,v) e` should look for free occurrences of `u` in `e` and replace them with `v`. Crucially, it should _not_ rename any bound occurrences of `u`, and it should take care that any free `u`s do not become bound when turned into `v`s. We can do this by case analysis on `e`.

> renameFreeE :: (Var Expr, Var Expr) -> Expr -> Expr
> renameFreeE (u,v) = \case
>   ECon !loc c -> ECon loc c

Constant expressions have no free variables to be renamed. That seems clear.

>   EVar !loc x -> EVar loc $ if x == u then v else x

The variable in a variable expression is always free; in this case, renaming the variable is straightforward. See if $x$ matches the variable $u$ to be renamed, and rename it if so.

>   ELam !loc x e ->
>     if x == u
>       then ELam loc x e
>       else if x /= v
>         then ELam loc x (renameFreeE (u,v) e)
>         else
>           let
>             y = fresh
>               [ S.fromList [u,v]
>               , freeExprVarsE e ]
>           in
>             ELam loc y
>               (renameFreeE (u,v) $ renameFreeE (x,y) e)

Lambda expressions are more interesting. If $u$ matches the variable at the binding site, then all occurrences of $u$ in the subexpression $e$ are bound -- no more renaming needs to be done, because there are no free $u$s. If $u$ _doesn't_ match the variable in the binding site then there may be free occurrences of $u$ in $e$, so we need to recursively rename them. But there's a risk. If $v$ doesn't match the variable at the binding site, we can rename free $u$s to $v$s in $e$. But if $v$ _does_ match the variable at the binding site, then just renaming $u$s to $v$s will turn free variables into bound variables. In this case we need to rename the free occurrences of the binding site variable. But we can't just call it anything; we have to make sure $y$ won't clash with any variables that are already free in $e$ or with either $u$ or $v$.

>   ELet !loc x e1 e2 ->
>     if x == u
>       then ELet loc x (renameFreeE (u,v) e1) e2
>       else if x /= v
>         then ELet loc x (renameFreeE (u,v) e1) (renameFreeE (u,v) e2)
>         else
>           let
>             y = fresh
>               [ S.fromList [u,v]
>               , freeExprVarsE e1
>               , freeExprVarsE e2 ]
>           in
>             ELet loc y
>               (renameFreeE (u,v) e1)
>               (renameFreeE (u,v) $ renameFreeE (x,y) e2)

Let expressions are also interesting; note the similarity to the lambda case. If $u$ matches the variable at the binding site, then there are no free occurrences of $u$ in $e_2$, but $u$ is not bound in $e_1$, so we have to rename it there. If $v$ doesn't match $x$, we can rename $u$ without capturing any free variables. If $v$ does match $x$, then we need to rename $x$ to something other than $u$ and $v$ that won't capture any other free variables in $e$.

>   EApp !loc e1 e2 ->
>     EApp loc (renameFreeE (u,v) e1) (renameFreeE (u,v) e2)

Application expressions don't bind any variables, so we can just recursively rename.

With `renameFreeE` in hand, we're now prepared to define equality for `Expr`s in a way that accounts for different dummy variable names. We'll do this by pattern matching on the form of the expressions. In all cases we don't care about the `Loc` parameter.

> instance Eq Expr where
>   e1 == e2 = case (e1,e2) of
>     (ECon !loc1 c1, ECon !loc2 c2) -> c1 == c2
>     (EVar !loc1 x1, EVar !loc2 x2) -> x1 == x2

Both constants and variables can be checked for equality syntactically; remember that "top level" variables are free.

>     (ELam !loc1 x1 e1, ELam !loc2 x2 e2) ->
>       if x1 == x2
>         then e1 == e2
>         else
>           let
>             y = fresh
>               [ freeExprVarsE e1
>               , freeExprVarsE e2 ]
>           in
>             (renameFreeE (x1,y) e1) == (renameFreeE (x2,y) e2)

If two lambda expressions use the same dummy variable, we can just check that their subexpressions are equal. If they have different dummy variables, though, we need to rename them to some common variable. The new variable name ($y$ here) should not be free in either $e_1$ or $e_2$, to prevent any free variables in the subexpressions from becoming bound.

>     (ELet !loc1 x1 e1 f1, ELet !loc2 x2 e2 f2) ->
>       (==)
>         (EApp loc1 (ELam loc1 x1 f1) e1)
>         (EApp loc2 (ELam loc2 x2 f2) e2)

For let expressions, we can use the equivalence $$\mathsf{let}\ x = e_1\ \mathsf{in}\ e_2 \Leftrightarrow (\lambda x . e_2)e_1.$$ Unlike the other recurrences in this definition, this one doesn't explicitly recurse on a smaller expression; however, it does recurse on an expression with strictly fewer `ELet` nodes, which is good enough to ensure it eventually terminates.

>     (EApp !loc1 e1 f1, EApp !loc2 e2 f2) ->
>       (e1 == e2) && (f1 == f2)

Application expressions don't bind any variables, so we can just recursively compare each branch.

>     _ -> False

And no other pairs of expressions are equal.

Equality on expressions should be "up to a hygienic renaming of bound variables"; that is, we should be able to rename bound variables in a capture-avoiding way and get an "equal" expression.

We can test this with some specific cases.

> test_cases_expr_eq :: Bool
> test_cases_expr_eq = and
>   [ (==)
>      (ELam Q (Var "x") (EVar Q (Var "x")))
>      (ELam Q (Var "y") (EVar Q (Var "y")))
> 
>   , (==)
>      (ELet Q (Var "x")
>        (EApp Q (ECon Q (Con "c")) (EVar Q (Var "x")))
>        (EVar Q (Var "x")))
>      (ELet Q (Var "y")
>        (EApp Q (ECon Q (Con "c")) (EVar Q (Var "x")))
>        (EVar Q (Var "y")))
> 
>   , (/=)
>      (ELet Q (Var "x")
>        (EApp Q (ECon Q (Con "c")) (EVar Q (Var "x")))
>        (EVar Q (Var "x")))
>      (ELet Q (Var "y")
>        (EApp Q (ECon Q (Con "c")) (EVar Q (Var "y")))
>        (EVar Q (Var "y")))
>   ]

The difference between the last two cases is subtle; it's important to understand why they should be true.

We should also check that this implementation of equality is actually an equivalence relation.

> test_eq_reflexive
>   :: (Eq t) => Proxy t -> t -> Bool
> test_eq_reflexive _ e =
>   e == e
> 
> test_eq_symmetric
>   :: (Eq t) => Proxy t -> t -> t -> Bool
> test_eq_symmetric _ e1 e2 =
>   (e1 == e2) == (e2 == e1)
> 
> test_eq_transitive
>   :: (Eq t) => Proxy t -> t -> t -> t -> Bool
> test_eq_transitive _ e1 e2 e3 =
>   if (e1 == e2) && (e2 == e3) then e1 == e3 else True

These tests, especially the symmetry and transitivity tests, are of dubious quality because it is very unlikely that our test case generator will produce pairs or triples of expressions that are all alpha equivalent. These should certainly pass if our implementation of equality is correct, but we shouldn't feel too good about it if they don't fail.

We'll also write a helper function that renames the _bound_ variables in an expression. Renaming bound variables will work differently from renaming free ones; rather than saying "rename this specific free variable" we'll say "make sure the bound variables in this expression do not appear in a given set".

> renameBoundE :: S.Set (Var Expr) -> Expr -> Expr
> renameBoundE avoid = \case
>   ECon !loc c -> ECon loc c
>   EVar !loc x -> EVar loc x
>   ELam !loc x e -> if S.member x avoid
>     then
>       let y = fresh [ avoid, freeExprVarsE e ] in
>       ELam loc y (renameBoundE avoid $ renameFreeE (x,y) e)
>     else ELam loc x (renameBoundE avoid e)
>   ELet !loc x e1 e2 -> if S.member x avoid
>     then
>       let y = fresh [ avoid, freeExprVarsE e2 ] in
>       ELet loc y
>         (renameBoundE avoid e1)
>         (renameBoundE avoid $ renameFreeE (x,y) e2)
>     else ELet loc x (renameBoundE avoid e1) (renameBoundE avoid e2)
>   EApp !loc e1 e2 ->
>     EApp loc (renameBoundE avoid e1) (renameBoundE avoid e2)



Renaming
--------

On the way to defining alpha equivalence for lambda terms we introduced three helper functions: one to collect the free variables in an expression, one to safely rename a free variable, and one to rename the bound variables. These operations are crucial to detecting alpha equivalence correctly. They will also make sense for other kinds of objects. To better understand how renaming variables behaves, we'll wrap them in a type class.

> class HasExprVars t where
>   freeExprVars :: t -> S.Set (Var Expr)
>   renameFreeExpr :: (Var Expr, Var Expr) -> t -> t
>   renameBoundExpr :: S.Set (Var Expr) -> t -> t
>
> instance HasExprVars Expr where
>   freeExprVars = freeExprVarsE
>   renameFreeExpr = renameFreeE
>   renameBoundExpr = renameBoundE

To be really useful a type class should satisfy at least one law, and `HasTypeVars` is no different. Let's think about what properties these functions should satisfy.

First, renaming a free variable removes it from the set of free variables.

> test_exprvars_rename_free
>   :: (HasExprVars t) => Proxy t -> Var Expr -> t -> Bool
> test_exprvars_rename_free _ x t =
>   let y = fresh [ S.singleton x ] in
>   S.notMember x (freeExprVars $ renameFreeExpr (x,y) t)

Renaming a free variable is a transposition, provided we rename to a variable that isn't already free.

> test_exprvars_rename_trans
>   :: (HasExprVars t, Eq t)
>   => Proxy t -> Var Expr -> t -> Bool
> test_exprvars_rename_trans _ x t =
>   let y = fresh [ freeExprVars t ] in
>   t == (renameFreeExpr (y,x) $ renameFreeExpr (x,y) t)

Renaming the bound variables does not change the set of free variables.

> test_exprvars_rename_bound
>   :: (HasExprVars t) => Proxy t -> S.Set (Var Expr) -> t -> Bool
> test_exprvars_rename_bound _ avoid t =
>   (freeExprVars t) == (freeExprVars $ renameBoundExpr avoid t)

Renaming the bound variables yields an equal expression; this is the whole point of alpha equivalence.

> test_exprvars_rename_eq
>   :: (HasExprVars t, Eq t) => Proxy t -> S.Set (Var Expr) -> t -> Bool
> test_exprvars_rename_eq _ avoid t =
>   t == renameBoundExpr avoid t

Side note -- these tests were very effective at helping me debug the variable renaming functions. :)



Expression Substitution
-----------------------

It will be useful later to lift this business about variables to expression substitutions; we'll do this pointwise.

> instance HasExprVars (Sub Expr) where
>   freeExprVars (Sub m) =
>     S.unions . map freeExprVars . M.elems $ m
>   renameFreeExpr (u,v) (Sub m) =
>     Sub $ fmap (renameFreeExpr (u,v)) m
>   renameBoundExpr avoid (Sub m) =
>     Sub $ fmap (renameBoundExpr avoid) m

It's worth thinking about why it makes sense to rename bound variables in a substitution pointwise. Are variables in the support free or bound? Well, neither, really. 'Free' and 'bound' only make sense in the context of an expression grammar, and substitutions are... not that. We can think of a substitution as a transformation waiting to be performed on some other thing, and the variables in the support act kind of like binding sites for variables _there_, but they are neither free nor bound in the substitution itself.

We also need an `Arbitrary` instance for expression substitutions.

> instance Arbitrary (Sub Expr) where
>   arbitrary = Sub <$> arbitrary
>   shrink (Sub m) = map Sub $ shrink m

We'll be applying expression substitutions to a few different sorts of things, so we'll wrap it in a type class. Again -- symbolic operators are usually bad form in my opinion, but this is not meant for use in other projects and the symbols make expressing properties much more clear.

> class SubExpr t where
>   ($>) :: Sub Expr -> t -> t

Certainly we should be able to apply an expression substitution to an `Expr`. This should replace any free variables by their images under the substitution but leave bound variables alone.

> instance SubExpr Expr where
>   s $> e = case e of
>     ECon !loc c -> ECon loc c

Constant expressions have no free variables to substitute. That seems clear.

>     EVar !loc x -> case applySub x s of
>       Nothing -> EVar loc x
>       Just e' -> e'

Variable expressions are free, so we look up the image of the variable under the substitution. Remember that if $s$ does not explicitly move a variable, it implicitly acts like the identity.

>     ELam !loc x e ->
>       let
>         y = fresh
>           [ S.singleton x
>           , freeExprVars e
>           , support s
>           , freeExprVars s ]
>       in
>         ELam loc y (s $> renameFreeE (x,y) e)

As usual, lambda expressions are interesting. We recursively substitute on the subexpression, but we only want to apply the substitution to free variables. To avoid messing up any occurrences of the _bound_ variable, we first rename it, making sure the new name does not clash with any free variables in the subexpression or any variables making an appearance in the substitution, either in the support or in the image. This is why we needed to implement `HasExprVars` for substitutions.

>     ELet !loc x e1 e2 ->
>       let
>         y = fresh
>           [ S.singleton x
>           , freeExprVars e2
>           , support s
>           , freeExprVars s ]
>       in
>         ELet loc y (s $> e1) (s $> renameFreeE (x,y) e2)

Let expressions are similar to lambdas. We apply the substitution recursively, making sure to first rename the free occurrences of the dummy variable -- but only in `e2`.

>     EApp !loc e1 e2 -> EApp loc (s $> e1) (s $> e2)

Again as usual, we substitute on an application expression by recursively substituting on each branch.

This is getting pretty abstract. We should check that substitution does something reasonable with a test case. Here we rename free occurrences of $x$ to $y$; note that the bound $x$ gets renamed, in this case to $w$.

> test_cases_sub_expr :: Bool
> test_cases_sub_expr = and
>   [ let
>       s = (Var "x") --> (EVar Q (Var "y"))
>       e1 = ELam Q (Var "z")
>              (EApp Q
>                (EVar Q (Var "x"))
>                (ELam Q (Var "x")
>                  (EApp Q (EVar Q (Var "y"))
>                  (EVar Q (Var "x")))))
>       e2 = ELam Q (Var "z")
>              (EApp Q
>                (EVar Q (Var "y"))
>                (ELam Q (Var "w")
>                  (EApp Q (EVar Q (Var "y"))
>                  (EVar Q (Var "w")))))
>     in s $> e1 == e2
>   ]

We can also apply one substitution to another "pointwise".

> instance SubExpr (Sub Expr) where
>   s1 $> (Sub m2) = Sub $ fmap (s1 $>) m2

Note that on substitutions, the _apply_ operator is a sort of multiplication. It would be nice if that multiplication were associative -- that is, if

    s1 $> (s2 $> s3) == (s1 $> s2) $> s3

for all `s1`, `s2`, and `s3`. Even better is if, as a semigroup, the set of substitutions acted on the set of expressions by substitution. Unfortunately this is not the case. It's not too hard to see a counterexample -- think about what happens when `s2` is the empty substitution.

But! This can be fixed with a small adjustment. Define a product on substitutions like so:

> instance Semigroup (Sub Expr) where
>   s1 <> s2 = (s1 $> s2) .& s1

Remember that `.&` is the _augmentation_ operator on substitutions; it augments `s1 $> s2` with any additional mapping done by `s1`. Intuitively, `s1 <> s2` is a substitution such that if `x` is in the support of `s2`, it gets mapped to some expression by `s2`, to which `s1` is then applied, and if `x` is not in the support of `s2`, just `s1` is applied. That sounds an awful lot like we had first applied `s2` and then `s1`. And indeed, adding in the empty substitution,

> instance Monoid (Sub Expr) where
>   mempty = emptySub

We can check that `Sub Expr` satisfies the monoid laws.

> test_monoid_identity
>   :: (Eq t, Monoid t) => Proxy t -> t -> Bool
> test_monoid_identity _ s = and
>   [ s == mempty <> s
>   , s == s <> mempty
>   ]
> 
> test_monoid_associative
>   :: (Eq t, Monoid t) => Proxy t -> t -> t -> t -> Bool
> test_monoid_associative _ s1 s2 s3 =
>   s1 <> (s2 <> s3) == (s1 <> s2) <> s3

And we can test that `$>` is a monoid action.

> test_subexpr_identity
>   :: (Eq t, SubExpr t) => Proxy t -> t -> Bool
> test_subexpr_identity _ t =
>   emptySub $> t == t
>
> test_subexpr_action
>   :: (Eq t, SubExpr t) => Proxy t -> Sub Expr -> Sub Expr -> t -> Bool
> test_subexpr_action _ s1 s2 t =
>   s1 $> (s2 $> t) == (s1 <> s2) $> t

Situations like this are where property checking really shines. A formal proof that `Sub Expr` is a monoid acting on `Expr` is possible, but tedious, and doesn't guarantee our implementation is bug-free. But a property test with a good test case generator is devastatingly effective at finding bugs -- and very satisfying when it passes.

We'll also need a utility for detecting when an expression substitution is trivial.

> trivialExprSub :: Sub Expr -> Bool
> trivialExprSub (Sub m) = all isId $ M.toList m
>   where
>     isId :: (Var Expr, Expr) -> Bool
>     isId (x,e) = case e of
>       EVar _ y -> x == y
>       _ -> False



Matching
--------

We need one last operation on expressions: matching. Given two expressions $E_1$ and $E_2$, a _matching_ is a substitution $S$ such that $S \cdot E_1 = E_2$. Matching will be handy later when we have an equation of lambda expressions that we'd like to treat as a rewrite rule; if $E_1 = F_1$, and if $S \cdot E_1 = E_2$, then we should have $E_2 = S \cdot F_2$. The matching algorithm will try to find $S$ given $E_1$ and $E_2$.

Matching is different from the algorithms we've seen so far; we're effectively solving for a substitution. Remember that substitutions only operate on the _free_ variables in an expression. So in a recursive strategy we'll need to keep track of which variables have been bound somewhere in the "outer expression". This means our matching strategy will need to carry some additional state that we didn't need when applying substitutions or deciding alpha equivalence. We'll achieve this by defining `matchExpr` in terms of a helper function, `matchExprInContext`, which takes as an additional argument a set of bound variables.

> matchExpr :: Expr -> Expr -> Maybe (Sub Expr)
> matchExpr = matchExprInContext S.empty

We start out with an empty context; no variables have been bound.

> matchExprInContext
>   :: S.Set (Var Expr) -> Expr -> Expr -> Maybe (Sub Expr)
> matchExprInContext bound u1 u2 = case (u1,u2) of
>   (ECon !loc1 c1, ECon !loc2 c2) ->
>     if c1 == c2
>       then Just mempty
>       else Nothing

One constant expression can be substituted to another precisely when the constants are identical, and in this case the empty substitution achieves this. In fact _any_ substitution would transform a constant to itself; but we can't use just any substitution here. We have a context of bound variables, and the substitution shouldn't cause any free variables to become bound. We will also eventually combine this substitution with others, so it needs to be as general as possible.

>   (EVar !loc1 x, e) -> if S.member x bound
>     then case e of
>       EVar _ y -> if x == y
>         then Just mempty
>         else Nothing
>       _ -> Nothing
>     else if S.disjoint bound (freeExprVars e)
>       then Just (x --> e)
>       else Nothing

Variable expressions are where matching happens. Naively, variables match anything -- but we need to be careful with the binding context.

If $x$ is bound in context, and we try to substitute an identical variable, then the empty substitution is a matching. If $x$ is bound in context and $e$ is _not_ an identical variable, then no substitution can take $x$ to $e$ because $x$ is not free.

If $x$ is free in context, then we can simply substitute $x \mapsto e$ provided no free variables in $e$ become bound in context. If they do, no substitution works. In this case we might complain that the bound variables that clash with free variables in $e$ could just be renamed. But we can't reach back into the superexpression and retroactively change the name of a bound variable. Instead, we'll have to rely on the binding sites above this node in the expression tree to have already renamed their bound variables to avoid capturing free variables in $e$.

>   (ELam !loc1 x1 e1, ELam !loc2 x2 e2) ->
>     if x1 == x2
>       then matchExprInContext (S.insert x1 bound) e1 e2
>       else do
>         let y = fresh [bound, freeExprVars e1, freeExprVars e2]
>         matchExprInContext
>           (S.insert y bound)
>           (renameFreeE (x1,y) e1)
>           (renameFreeE (x2,y) e2)

Lambda... if the two lambda terms use exactly the same dummy variable, then we add that variable to the bound context and recursively match on the subexpressions. If the dummy variables are not identical then we rename them to some $y$ _that doesn't capture any free variables in either subexpression_ and then recurse. This is how we account for the need to avoid variable capture when matching free variables.

We also make sure $y$ doesn't clash with a variable that's already been bound; this part isn't strictly necessary because of the way bound variable name clashes resolve, but it makes me feel better.

>   (ELet !loc1 x1 e1 f1, ELet !loc2 x2 e2 f2) ->
>     matchExprInContext bound
>       (EApp loc1 (ELam loc1 x1 f1) e1)
>       (EApp loc2 (ELam loc2 x2 f2) e2)

For let expressions, we can take advantage of the lambda equivalent expression. Again, this is not strictly recursion on a smaller expression, but it is recursion on an expression with strictly fewer let terms.

>   (EApp !loc1 e1 f1, EApp !loc2 e2 f2) -> do
>     s1 <- matchExprInContext bound e1 e2
>     s2 <- matchExprInContext bound f1 f2
>     unionSub s1 s2

For application terms we can match each branch independently and union them together. Recall that `unionSub` returns `Nothing` if we give it incompatible substitutions, which in this case corresponds to a free variable that "matches" two distinct subexpressions.

>   _ -> Nothing

No other pairs of expressions match.

Let's check our intuition about matching with some test cases. Keep in mind that if matching succeeds against expressions $E_1$ and $E_2$, the result is a substitution $S$ such that $S \cdot E_1 = E_2$.

This example matches against a single variable. The notation is tedious to follow, but the two expressions here are $x$ and $yz$.

> test_cases_expr_match :: Bool
> test_cases_expr_match = and
>   [ (==)
>       (matchExpr
>         (EVar Q (Var "x"))
>         (EApp Q (EVar Q (Var "y")) (EVar Q (Var "z"))))
>       (Just $ Sub $ M.fromList
>         [ (Var "x", EApp Q (EVar Q (Var "y")) (EVar Q (Var "z")))
>         ])

This example matches two lambda expressions with different dummy variables: $\lambda x . yx$ and $\lambda p . zp$.

>   , (==)
>       (matchExpr
>         (ELam Q (Var "x")
>           (EApp Q (EVar Q (Var "y")) (EVar Q (Var "x"))))
>         (ELam Q (Var "p")
>           (EApp Q (EVar Q (Var "z")) (EVar Q (Var "p")))))
>       (Just $ Sub $ M.fromList
>         [ (Var "y", EVar Q (Var "z"))
>         ])

This example matches two different occurrences of the same free variable: in $x(\lambda y . x)$ against $c(\lambda z . c)$, where $c$ is a constant.

>   , (==)
>       (matchExpr
>         (EApp Q
>           (EVar Q (Var "x"))
>           (ELam Q (Var "y") (EVar Q (Var "x"))))
>         (EApp Q
>           (ECon Q (Con "c"))
>           (ELam Q (Var "z") (ECon Q (Con "c")))))
>       (Just $ Sub $ M.fromList
>         [ (Var "x", ECon Q (Con "c"))
>         ])

This example matches two different occurrences of the same free variable, but this time the matches are not compatible: $x(\lambda y . x)$ and $c(\lambda z . d)$, where $c$ and $d$ are distinct constants.

>   , (==)
>       (matchExpr
>         (EApp Q
>           (EVar Q (Var "x"))
>           (ELam Q (Var "y") (EVar Q (Var "x"))))
>         (EApp Q
>           (ECon Q (Con "c"))
>           (ELam Q (Var "z") (ECon Q (Con "d")))))
>       Nothing

This example attempts to match the identity function with a constant function: $\lambda x . y$ and $\lambda x . x$. This pair showed up often as a counterexample while debugging.

>   , (==)
>       (matchExpr
>         (ELam Q (Var "x") (EVar Q (Var "y")))
>         (ELam Q (Var "x") (EVar Q (Var "x"))))
>       Nothing
>   ]

Because matching is defined abstractly as the solution to an equation -- specifically, $S \cdot E_1 = E_2$ -- we have some natural property tests. First, we can verify that any substitutions returned by matching satisfies this equation.

> test_expr_match_sub
>   :: Expr -> Expr -> Bool
> test_expr_match_sub e1 e2 =
>   case matchExpr e1 e2 of
>     Nothing -> True
>     Just s -> e2 == s $> e1

Matching should also be "transitive" in the sense that if $S \cdot E_1 = E_2$ and $T \cdot E_2 = E_3$, then $TS \cdot E_1 = E_3$.

> test_expr_match_transitive
>   :: Expr -> Expr -> Expr -> Bool
> test_expr_match_transitive e1 e2 e3 =
>   case (matchExpr e1 e2, matchExpr e2 e3) of
>     (Just s1, Just s2) -> e3 == (s2 <> s1) $> e1
>     _ -> True

Those two properties are decent as canaries; they should definitely pass if our implementation of match is correct. They have a significant downside though -- the vast majority of pairs of expressions do not match, and the probability of a match falls of quickly as the expressions get bigger. So most of the test cases they generate will give us no information.

Another way to check matching is to give it two expressions we've cooked up to match. The simplest thing I can think of is to match an expression against itself. This should always succeed, and moreover, should succeed with a trivial substitution.

> test_expr_match_self
>   :: Expr -> Bool
> test_expr_match_self e =
>   case matchExpr e e of
>     Nothing -> False
>     Just s -> trivialExprSub s

Note that we use the predicate `trivialExprSub` here, rather than checking that $s$ is literally the empty substitution. This is because of the recursive way in which matching is done; in particular, on the application form. In addition to keeping track of what variables get mapped to, we have to keep track of which variables have been seen, to avoid unioning incompatible substitutions.

For another test, every expression should match itself via a trivial substitution after we rename the bound variables.

> test_expr_match_rename
>   :: S.Set (Var Expr) -> Expr -> Bool
> test_expr_match_rename avoid e =
>   case matchExpr e (renameBoundExpr avoid e) of
>     Nothing -> False
>     Just s -> trivialExprSub s

Another pair of expressions that should always match are $E$ and $S \cdot E$ for some expression $E$ and substitution $S$. One caveat is that in general, the substitution that match finds will not necessarily be equal to $T$; for instance, the support of $S$ might include variables that aren't free in $E$. But we should have $S \cdot E = T \cdot E$.

> test_expr_sub_match
>   :: Sub Expr -> Expr -> Bool
> test_expr_sub_match s1 e =
>   case matchExpr e (s1 $> e) of
>     Nothing -> False
>     Just s2 -> (s2 $> e) == (s1 $> e)

This test has the advantage that it doesn't generate useless cases.



Recap
-----

So far we've developed a grammar for lambda calculus with let bindings. We've defined what it means for a variable in a lambda expression to be _free_ or _bound_, and have defined helpers for renaming the free and bound variables in an expression. We can _apply_ a variable substitution to an expression, and given two expressions, can construct a substitution taking one to the other if such a thing exists.

Next we will develop a grammar of _types_ and see how it is possible to efficiently assign a type to some lambda expressions.
