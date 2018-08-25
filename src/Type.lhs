---
title: Types
---

So far we've defined a grammar of [_lambda expressions_](./Expr.html) and thought very hard about how to perform substitutions on them. In this module we'll develop a grammar of _types_, with an eye toward implementing a Hindley-Milner style type inference algorithm.

Inductively defined expression grammars (like `Expr`) generate a set of expressible expressions. Type systems make it possible to impose additional restrictions on which of these expressible expressions are _meaningful_; a type system assigns a _type_ to some subset of expressions. Verifying that a given expression has a certain type or that two expressions have the same type is called _type checking_, and this check can help prevent or even rule out some classes of semantic errors.

That's the good news about types. The bad news is that if a type system is ad-hoc, bolted on, or otherwise poorly thought out then it will need lots of hand-holding to work properly.

Lambda calculus with let expressions has a type system with the following nice properties:

1. Every lambda expression can be efficiently assigned a type (or found to be untypeable).
2. The type of an expression can be _inferred_ without requiring any explicit type annotations.

That second property in particular, type inference, is a killer feature. It means we can get the benefits of strong, strict, static types without any syntactic overhead. This is the gist of the famous [_Hindley-Milner type system_](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) that underlies ML-family programming languages.

But before we can think about inference, we have to nail down a grammar of types.

As usual we start with some module imports.

> {-# LANGUAGE LambdaCase, FlexibleInstances #-}
> module Type where
> 
> import qualified Data.Map as M
>   ( difference, fromSet, elems, fromList, toList )
> import Data.Proxy
>   ( Proxy(..) )
> import qualified Data.Set as S
>   ( Set(..), empty, singleton, delete, insert, toList
>   , member, union, unions, disjoint, fromList, difference )
> import Test.QuickCheck
>   ( Arbitrary(..), Gen, elements, oneof, getSize )
>
> import Var
> import Sub
> import Expr



Monotypes
---------

Types come in two flavors: _monotypes_ and _polytypes_; the difference between the two is roughly that polytypes have explicitly quantified bound variables while monotypes do not. This makes it possible to force all quantifiers to appear at the "top level" of a type expression, which is important in the proof that type inference is decidable. But we don't need to worry about the details of that.

There are essentially 4 different kinds of monotypes.

1. **Type constants**, which represent a specific, concrete type.
2. **Type variables**, which in practice will always be universally quantified, but in the context of monotypes can be thought of as free.
3. **Arrow types**, typically notated $\alpha \rightarrow \beta$, which represent functions.
4. **Type constructors**, which are sort of like functions at the type level. This is the mechanism for wrapping multiple types into one "structure".

We'll represent these with the following Haskell type. Again note the complication of an extra `Loc` parameter; this will be used later.

> data MonoType
>   = TCon Loc (Con MonoType)
>   | TVar Loc (Var MonoType)
>   | TArr Loc MonoType MonoType
>   | TSt1 Loc (Con MonoType) MonoType
>   | TSt2 Loc (Con MonoType) MonoType MonoType
>   deriving (Show)
> 
> instance Eq MonoType where
>   m1 == m2 = case (m1,m2) of
>     (TCon _ c1, TCon _ c2) -> c1 == c2
>     (TVar _ x1, TVar _ x2) -> x1 == x2
>     (TArr _ u1 v1, TArr _ u2 v2) ->
>       (u1 == u2) && (v1 == v2)
>     (TSt1 _ c1 u1, TSt1 _ c2 u2) ->
>       (c1 == c2) && (u1 == u2)
>     (TSt2 _ c1 u1 v1, TSt2 _ c2 u2 v2) ->
>       (c1 == c2) && (u1 == u2) && (v1 == v2)
>     _ -> False

We've altered the usual type grammar slightly. The full development of HM type inference allows for type constructors of arbitrary arity, but we're restricting ourselves to just two: `TSt1` and `TSt2`.

Our `Eq` instance is almost syntactic equality, except that we disregard the `loc` parameters. This is safe because monotypes have no binding constructs, so there's no alpha equivalence to worry about.

Monotypes also have a notion of free variables -- although it's a boring one since _all_ variables in a monotype are free. We will be finding the free type variables of other objects so we'll wrap this in a type class (as we did with expression variables).

> class FreeTypeVars t where
>   freeTypeVars :: t -> S.Set (Var MonoType)
> 
> instance FreeTypeVars MonoType where
>   freeTypeVars x = case x of
>     TCon _ _ -> S.empty
>     TVar _ x -> S.singleton x
>     TArr _ a b -> S.union (freeTypeVars a) (freeTypeVars b)
>     TSt1 _ _ a -> freeTypeVars a
>     TSt2 _ _ a b -> S.union (freeTypeVars a) (freeTypeVars b)

While we're here, we also need an `Arbitrary` instance for generating `MonoType`s. This generator is very similar to the one we defined for `Expr`s; we keep track of a depth parameter and make sure it shrinks on every recursive call.

> instance Arbitrary MonoType where
>   arbitrary = getSize >>= genDepth
>     where
>       genDepth :: Int -> Gen MonoType
>       genDepth k
>         | k <= 0 = oneof
>             [ TCon <$> arbitrary <*> arbitrary
>             , TVar <$> arbitrary <*> arbitrary
>             ]
>         | otherwise = do
>             let recur = genDepth =<< elements [0..(k-1)]
>             oneof
>               [ TArr <$> arbitrary <*> recur <*> recur
>               , TSt1 <$> arbitrary <*> arbitrary <*> recur
>               , TSt2 <$> arbitrary <*> arbitrary <*> recur <*> recur
>               ]
> 
>   shrink = \case
>     TCon _ _ -> []
>     TVar _ _ -> []
>     TArr loc a b ->
>       [ a, b ] ++
>       [ TArr loc u v | u <- shrink a, v <- shrink b ] ++
>       [ TArr loc a v | v <- shrink b ] ++
>       [ TArr loc u b | u <- shrink a ]
>     TSt1 loc c a ->
>       [ a ] ++
>       [ TSt1 loc c u | u <- shrink a ]
>     TSt2 loc c a b ->
>       [ a, b ] ++
>       [ TSt2 loc c u v | u <- shrink a, v <- shrink b ] ++
>       [ TSt2 loc c a v | v <- shrink b ] ++
>       [ TSt2 loc c u b | u <- shrink a ]
> 
> instance Arbitrary (Var MonoType) where
>   arbitrary = do
>     let makeVar i = Var $ 'x' : show i
>     k <- getSize
>     makeVar <$> elements [0..k]
> 
> instance Arbitrary (Con MonoType) where
>   arbitrary = do
>     let makeCon i = Con $ 'C' : show i
>     k <- getSize
>     makeCon <$> elements [0..k]



Monotype Substitutions
----------------------

As with expression substitutions, we'll be making monotype substitutions on several kinds of objects. Let's wrap this substitution behind a type class.

> class SubMono t where
>   ($.) :: Sub MonoType -> t -> t

We also need an `Arbitrary` instance for `MonoType` substitutions.

> instance Arbitrary (Sub MonoType) where
>   arbitrary = Sub <$> arbitrary
>   shrink (Sub m) = map Sub $ shrink m

The most basic kind of monotype substitution is on a `MonoType` expression. This substitution is particularly simple because `MonoType`s have no bound variables.

> instance SubMono MonoType where
>   s $. t = case t of
>     TCon loc c -> TCon loc c
>     TVar loc x -> case applySub x s of
>       Nothing -> TVar loc x
>       Just t' -> t'
>     TArr loc a b ->
>       TArr loc (s $. a) (s $. b)
>     TSt1 loc c a ->
>       TSt1 loc c (s $. a)
>     TSt2 loc c a b ->
>       TSt2 loc c (s $. a) (s $. b)

Because `MonoType`s have no bound variables, monotype substitutions also have no bound variables. The set of free type variables in a substitution is the union of the free variable sets of its images.

> instance FreeTypeVars (Sub MonoType) where
>   freeTypeVars (Sub m) = S.unions . map freeTypeVars . M.elems $ m

As with expression substitutions, we can substitute one monotype expression into another:

> instance SubMono (Sub MonoType) where
>   s1 $. (Sub m2) = Sub $ fmap (s1 $.) m2

And use this to make the set of monotype substitutions a monoid.

> instance Semigroup (Sub MonoType) where
>   s1 <> s2 = (s1 $. s2) .& s1
>
> instance Monoid (Sub MonoType) where
>   mempty = emptySub

So `Sub MonoType` is a monoid; in fact `$.` should be a monoid action of `Sub MonoType` on `t`.

> test_submono_identity
>   :: (Arbitrary t, SubMono t, Eq t)
>   => Proxy t -> t -> Bool
> test_submono_identity _ t =
>   t == mempty $. t
> 
> test_submono_action
>   :: (Arbitrary t, SubMono t, Eq t)
>   => Proxy t -> Sub MonoType -> Sub MonoType -> t -> Bool
> test_submono_action _ s1 s2 t =
>   (s1 $. (s2 $. t)) == ((s1 <> s2) $. t)

We also need a helper for detecting when a type substitution is trivial.

> trivialMonoTypeSub :: Sub MonoType -> Bool
> trivialMonoTypeSub (Sub m) = all isId $ M.toList m
>   where
>     isId :: (Var MonoType, MonoType) -> Bool
>     isId (x,e) = case e of
>       TVar _ _ -> True
>       _ -> False



Unification
-----------

Suppose we have two types $T_1$ and $T_2$. If we can find a substitution $S$ such that $S \cdot T_1 = S \cdot T_2$, then we say $S$ is a _unifier_ for $T_1$ and $T_2$.

The existence of a unifier for two types is very special; it acts as a witness that the two expressions are "almost" the same. In general, if two types have a unifier, then they have infinitely many unifiers. This is because substitution is a monoid action; if $S$ is a unifier and $U$ an arbitrary substitution, we have $$(U \ast S) \cdot T_1 = U \cdot (S \cdot T_1) = U \cdot (S \cdot T_2) = (U \ast S) \cdot T_2,$$ letting $\ast$ denote substitution composition.

Some grammars have the additional property that _if_ two expressions are unifiable, then they have a unique special unifier $M$ such that _every_ unifier factors through $M$. Whenever something exists and is unique, it's handy to give it a name. So this unique 'minimal' unifier of two expressions, when it exists, is called the _most general unifier_ of $E_1$ and $E_2$. Whether or not most general unifiers exist depends on the details of the grammar -- and it turns out that for monotypes, MGUs do exist.

We can put the function which computes most general unifiers behind a type class for easy reuse.

> class (SubMono t) => UnifyTypes t where
>   unifyTypes :: t -> t -> Either UnificationError (Sub MonoType)

The basic signature for a `unify`-like function should be something like $$t \times t \rightarrow \mathsf{Sub}\ t,$$ but we need to add a complication. Given two arbitrary expressions, unification will almost certainly fail, and it will fail in one of only a few predictable ways. The `UnificationError` type enumerates these failure modes.

> data UnificationError
>   = CannotUnify MonoType MonoType
>   | OccursCheck (Var MonoType) MonoType
>   | VariableCapture (Var MonoType)
>   | FreeVariableCapture (Var MonoType)
>   | BoundVariableCapture (Var MonoType)
>   | IncompatibleSub
>   deriving (Eq, Show)

Before we define `unifyTypes` for `MonoType`, we need a utility function. `MonoType`s have no bound variables, but later we'll need to unify things that do. So we first define `unifyTypesInContext`. This function takes two monotypes, as well as sets of variables which are taken to be bound in context for each one. We then construct a unifier substitution, as well as two substitutions representing a bijection between the sets of bound variables. This is a little more complicated than the analogous operation in `matchExprInContext` because type variable binding will happen all at once at the "top level".

> unifyTypesInContext
>   :: (MonoType, S.Set (Var MonoType))
>   -> (MonoType, S.Set (Var MonoType))
>   -> Either UnificationError
>        (Sub MonoType, (Sub MonoType, Sub MonoType))
> 
> unifyTypesInContext (t1, bound1) (t2, bound2) = unify (t1,t2)
>   where
>     unify
>       :: (MonoType, MonoType)
>       -> Either UnificationError
>            (Sub MonoType, (Sub MonoType, Sub MonoType))
>     unify (t1,t2) = case (t1,t2) of
>       (TCon _ c1, TCon _ c2) ->
>         if c1 == c2
>           then Right (mempty, (mempty, mempty))
>           else Left $ CannotUnify t1 t2

Constant expressions unify precisely when they are identical, and in this case are unified by the empty substitution.

>       (TVar _ x1, e2) -> captureCheck x1 e2 bound1 bound2
>       (e1, TVar _ x2) -> captureCheck x2 e1 bound2 bound1

Unifying variable expressions with arbitrary expressions requires some care, so we'll defer this for now.

>       (TArr _ a1 b1, TArr _ a2 b2) -> do
>         (s1,(u1,v1)) <- unify (a1, a2)
>         (s2,(u2,v2)) <- unify (s1 $. b1, s1 $. b2)
>         let
>           m = do
>             u <- unionSub u1 u2
>             v <- unionSub v1 v2
>             return (u,v)
>         case m of
>           Nothing -> Left $ IncompatibleSub
>           Just (u,v) -> Right (s2 <> s1, (u,v))

To unify arrow types, we first unify the left hand side of the arrows, apply the resulting substitution to the right hand sides and unify them, and then compose the two substitutions (in the right order). We also need to make sure the binding context bijections are compatible; this is what the `unionSub`s are doing.

>       (TSt1 _ c1 a1, TSt1 _ c2 a2) -> 
>         if c1 == c2
>           then unify (a1, a2)
>           else Left $ CannotUnify t1 t2
> 
>       (TSt2 _ c1 a1 b1, TSt2 _ c2 a2 b2) ->
>         if c1 == c2
>           then do
>             (s1,(u1,v1)) <- unify (a1, a2)
>             (s2,(u2,v2)) <- unify (s1 $. b1, s1 $. b2)
>             let
>               m = do
>                 u <- unionSub u1 u2
>                 v <- unionSub v1 v2
>                 return (u,v)
>             case m of
>               Nothing -> Left $ IncompatibleSub
>               Just (u,v) -> Right (s2 <> s1, (u,v))
>           else Left $ CannotUnify t1 t2

Constructor types are not very different from arrow types. If we wanted to allow constructor types with more parameters, this pattern would continue.

>       _ -> Left $ CannotUnify t1 t2

And no other pairs of monotypes unify.

Now to handle unifying variables. First we check that the variable is not bound, or else that both expressions consist of only a bound variable. In the second case we note the bound pair as part of the binding context bijection.

>     captureCheck
>       :: Var MonoType -> MonoType
>       -> S.Set (Var MonoType) -> S.Set (Var MonoType)
>       -> Either UnificationError
>            (Sub MonoType, (Sub MonoType, Sub MonoType))
>     captureCheck x1 e bd1 bd2 = if S.member x1 bd1
>         then case e of
>           TVar _ x2 -> if S.member x2 bd2
>             then Right (mempty, (x1 --> TVar Q x2, x2 --> TVar Q x1))
>             else Left $ FreeVariableCapture x1
>           _ -> Left $ VariableCapture x1
>         else if S.disjoint bd2 (freeTypeVars e)
>           then bindVar x1 e
>           else Left $ BoundVariableCapture x1

Unifying a variable with an identical variable is achieved with the empty substitution.

>     bindVar
>       :: Var MonoType -> MonoType
>       -> Either UnificationError
>            (Sub MonoType, (Sub MonoType, Sub MonoType))
>     bindVar x (TVar _ y) | x == y = Right (mempty, (mempty, mempty))

For any other kind of expression, we can unify as long as the variable being substituted does not also appear (free, but this is redundant) in the expression. Why is this important? Remember that unification is trying to construct an $S$ such that $S \cdot E_1 = S \cdot E_2$. If $E_1 = x$, and if $x$ is free in $E_2$ but $E_2 \neq x$, then any substitution with $x$ in the support cannot possibly make these equal. We report this as an _occurs check_ violation.

>     bindVar x e = if S.member x $ freeTypeVars e
>       then Left $ OccursCheck x e
>       else Right (x --> e, (mempty, mempty))

Now we can unify `MonoType`s using `unifyTypesInContext`. In this case there is no context to worry about.

> instance UnifyTypes MonoType where
>   unifyTypes x y = do
>     (s,_) <- unifyTypesInContext (x, S.empty) (y, S.empty)
>     return s

And that's it for monotype unification. We can check that the substitution found by `unify` satisfies the equation $S \cdot E_1 = S \cdot E_2$ with a property test.

> test_unify_eq
>   :: (Eq t, UnifyTypes t)
>   => Proxy t -> t -> t -> Bool
> test_unify_eq _ t1 t2 = case unifyTypes t1 t2 of
>   Right s -> (s $. t1) == (s $. t2)
>   Left _ -> True

Another property is that every expression should unify with itself via the empty substitution.

> test_unify_self_empty
>   :: (Eq t, UnifyTypes t)
>   => Proxy t -> t -> Bool
> test_unify_self_empty _ t = case unifyTypes t t of
>   Right s -> s == emptySub
>   Left _ -> False

Unification should also be symmetric: $(t_1,t_2)$ and $(t_2,t_1)$ should either both unify or both fail to unify.

> test_unify_symmetric
>   :: (Eq t, UnifyTypes t)
>   => Proxy t -> t -> t -> Bool
> test_unify_symmetric _ t1 t2 =
>   case (unifyTypes t1 t2, unifyTypes t2 t1) of
>     (Right _, Right _) -> True
>     (Left _, Left _) -> True
>     _ -> False

Unifiability should also be "down closed". This needs some explanation. We can impose a kind of order on monotype expressions by saying $t_1 \leq t_2$ if $t_2 = S \cdot t_1$ for some substitution. It's not too hard to see that this order is reflexive and transitive. It may also be antisymmetric, but I'm too lazy to convince myself of that and we don't really need it. Say two expressions $S \cdot E_1$ and $S \cdot E_2$ unify; that is, we have $TS \cdot E_1 = TS \cdot E_2$. Then $E_1$ and $E_2$ also unify. This property is sometimes called _down closure_ because in order language it says that whenever $a_1 \leq b_1$ and $a_2 \leq b_2$ and $b_1 \sim b_2$, we also have $a_1 \sim a_2$.

> test_unify_down_closed
>   :: (Eq t, UnifyTypes t)
>   => Proxy t -> t -> t -> Sub MonoType -> Bool
> test_unify_down_closed _ t1 t2 s =
>   case unifyTypes (s $. t1) (s $. t2) of
>     Left _ -> True
>     Right _ -> case unifyTypes t1 t2 of
>       Left _ -> False
>       Right _ -> True



Polytypes
---------

Now for polytypes. A _polytype_ is just a monotype together with some (possibly empty) set of explicitly quantified variables. Note that there may be quantified variables that do not appear in the monotype; this is OK, and we should be able to toss out such variables without changing the meaning of the polytype.

> data PolyType = ForAll (S.Set (Var MonoType)) MonoType
>   deriving (Show)

We'll need an `Arbitrary` instance.

> instance Arbitrary PolyType where
>   arbitrary = ForAll <$> arbitrary <*> arbitrary
> 
>   shrink (ForAll as tau) =
>     [ ForAll bs psi | bs <- shrink as, psi <- shrink tau ] ++
>     [ ForAll as psi | psi <- shrink tau ] ++
>     [ ForAll bs tau | bs <- shrink as ]

And finding the free variables of a polytype is simple enough -- find the free variables of the monotype, and toss out any in the quantified set.

> instance FreeTypeVars PolyType where
>   freeTypeVars (ForAll as tau) =
>     S.difference (freeTypeVars tau) as

Note that we didn't derive equality for polytypes; as for expressions, syntactic equality on polytypes is too strict because it doesn't account for alpha equivalence.

Actually detecting alpha equivalence is a little different for polytypes than for expressions, because the bindings all happen at the "top level", rather than throughout the structure. Rather than just detecting whether or not two polytypes are alpha equivalent, we'll construct an explicit pair of substitutions, called an _alpha witness_, that maps their respective monotypes to each other.

> alphaWitness
>   :: PolyType
>   -> PolyType
>   -> Maybe (Sub MonoType, Sub MonoType)
> alphaWitness (ForAll as u) (ForAll bs v) = witness (u,v)
>   where
>     witness
>       :: (MonoType, MonoType)
>       -> Maybe (Sub MonoType, Sub MonoType)
>     witness = \case
>       (TCon _ c1, TCon _ c2) ->
>         if c1 == c2
>           then Just (emptySub, emptySub)
>           else Nothing

If two constant expressions are identically equal, they are alpha equivalent via the empty substitutions.

>       (TVar _ x1, TVar _ x2) ->
>         case (S.member x1 as, S.member x2 bs) of
>           (True, True) ->
>             Just (x1 --> TVar Q x2, x2 --> TVar Q x1)
>           (False, False) ->
>             if x1 == x2
>               then Just (emptySub, emptySub)
>               else Nothing
>           _ -> Nothing

Given two variable expressions, we first check whether either is bound in its polytype. If both are bound, then they are alpha equivalent via a transposition. If both are free, they are alpha equivalent only if they are identically equal, and in this case via the empty substitutions. If one is bound and the other is free, they cannot be alpha equivalent.

>       (TArr _ a1 b1, TArr _ a2 b2) -> do
>         (u1,v1) <- witness (a1,a2)
>         (u2,v2) <- witness (b1,b2)
>         w1 <- unionSub u1 u2
>         w2 <- unionSub v1 v2
>         return (w1,w2)

Given two arrow types, we first try to find an alpha witness for each end of the arrow, and then try to union them together. Remember that `unionSub` tries to union two substitutions as sets, and fails if they aren't compatible.

>       (TSt1 _ c1 a1, TSt1 _ c2 a2) ->
>         if c1 == c2
>           then witness (a1,a2)
>           else Nothing
> 
>       (TSt2 _ c1 a1 b1, TSt2 _ c2 a2 b2) ->
>         if c1 == c2
>           then do
>             (u1,v1) <- witness (a1,a2)
>             (u2,v2) <- witness (b1,b2)
>             w1 <- unionSub u1 u2
>             w2 <- unionSub v1 v2
>             return (w1,w2)
>           else Nothing

Type constructors are similar to arrow types, with the caveat that the constructor names have to be identical.

>       _ -> Nothing

No other pairs of polytypes are alpha equivalent.

Now two polytypes are equal precisely when they have an alpha witness.

> instance Eq PolyType where
>   p1 == p2 = case alphaWitness p1 p2 of
>     Nothing -> False
>     Just _ -> True

Because we're not deriving the usual syntactic equality for `PolyType`s, it's worthwhile to make sure it makes sense. First some test cases.

> test_cases_polytype_eq :: Bool
> test_cases_polytype_eq = and
>   [ (/=)
>       (ForAll S.empty (TVar Q (Var "a")))
>       (ForAll S.empty (TVar Q (Var "b")))
> 
>   , (/=)
>       (ForAll S.empty (TVar Q (Var "a")))
>       (ForAll (S.fromList [Var "a"]) (TVar Q (Var "a")))
> 
>   , (==)
>       (ForAll (S.fromList [Var "a"])
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "a"))))
>       (ForAll (S.fromList [Var "b"])
>         (TArr Q (TVar Q (Var "b")) (TVar Q (Var "b"))))
> 
>   , (/=)
>       (ForAll (S.fromList [Var "a"])
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "a"))))
>       (ForAll (S.fromList [Var "b"])
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "b"))))
> 
>   , (/=)
>       (ForAll (S.fromList [Var "a"])
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "a"))))
>       (ForAll (S.fromList [Var "a", Var "b"])
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "b"))))
> 
>   , (==)
>       (ForAll (S.fromList [Var "a"])
>         (TSt1 Q (Con "C") (TVar Q (Var "a"))))
>       (ForAll (S.fromList [Var "b"])
>         (TSt1 Q (Con "C") (TVar Q (Var "b"))))
> 
>   , (/=)
>       (ForAll (S.fromList [Var "a"])
>         (TSt1 Q (Con "C") (TVar Q (Var "a"))))
>       (ForAll (S.fromList [Var "a"])
>         (TSt1 Q (Con "D") (TVar Q (Var "a"))))
>   ]

We can introduce a utility function to rename the bound variables of a polytype. Specifically, this function will rename the bound variables appearing in one set, avoiding names that appear in some other sets.

> renameBoundT
>   :: [S.Set (Var MonoType)]
>   -> S.Set (Var MonoType)
>   -> PolyType
>   -> PolyType
> renameBoundT avoids vars t = foldr rename t $ S.toList vars
>   where
>     rename :: Var MonoType -> PolyType -> PolyType
>     rename x (ForAll as t) =
>       if S.member x as
>         then
>           let z = fresh $ as : (freeTypeVars t) : avoids in
>           ForAll (S.insert z $ S.delete x as) ((x --> TVar Q z) $. t)
>         else ForAll as t

Renaming bound variables should yield an identical polytype.

> test_polytype_eq_renames
>   :: PolyType -> [S.Set (Var MonoType)] -> S.Set (Var MonoType) -> Bool
> test_polytype_eq_renames t avoids xs = and
>   [ t == renameBoundT avoids xs t
>   , renameBoundT avoids xs t == t
>   ]

We can also apply a monotype substitution to a polytype, taking care to rename the bound variables if needed.

> instance SubMono PolyType where
>   s $. (ForAll as tau) =
>     let
>       s2 = s </ as
>       bs = freeTypeVars s2
>     in
>       if S.disjoint bs as
>         then ForAll as (s2 $. tau)
>         else
>           let avoids = [ bs, as, freeTypeVars tau ] in
>           s2 $. renameBoundT avoids as (ForAll as tau)

Finally, we can unify polytypes. We rename the bound variables first to ensure that no variables are free in one polytype and bound in the other.

> instance UnifyTypes PolyType where
>   unifyTypes t1@(ForAll bs1 _) t2@(ForAll bs2 _) = do
>     let ForAll as1 tau1 = renameBoundT [freeTypeVars t2] bs1 t1
>     let ForAll as2 tau2 = renameBoundT [freeTypeVars t1] bs2 t2
>     (s,_) <- unifyTypesInContext (tau1, as1) (tau2, as2)
>     return s

In addition to the generated tests for unification, here are some specific test cases that came up in debugging.

> test_cases_unify_polytype :: Bool
> test_cases_unify_polytype = and

First we have the signature of the identity function, written with two different dummy variables. These should unify with the empty substitution.

>   [ let
>       x = ForAll (S.fromList [Var "x0"])
>         (TArr Q (TVar Q (Var "x0")) (TVar Q (Var "x0")))
>       y = ForAll (S.fromList [Var "x1"])
>         (TArr Q (TVar Q (Var "x1")) (TVar Q (Var "x1")))
>     in
>       (==)
>         (unifyTypes x y)
>         (Right $ Sub (M.fromList []))

Next we have the signatures of two specialized identity functions; one on $x_0$ and one on $x_1$. These should unify via the substitution taking $x_0$ to $x_1$.

>   , let
>       x = ForAll (S.fromList [])
>         (TArr Q (TVar Q (Var "x0")) (TVar Q (Var "x0")))
>       y = ForAll (S.fromList [])
>         (TArr Q (TVar Q (Var "x1")) (TVar Q (Var "x1")))
>     in
>       (==)
>         (unifyTypes x y)
>         (Right $ Sub (M.fromList [(Var "x0", TVar Q (Var "x1"))]))

The next example should fail to unify; in this case we have a free variable being captured. Namely $w$.

>   , let
>       x = ForAll (S.fromList [Var "x0"])
>         (TArr Q (TVar Q (Var "x0")) (TVar Q (Var "x0")))
>       y = ForAll (S.fromList [Var "x1"])
>         (TArr Q (TVar Q (Var "x1")) (TVar Q (Var "w")))
>     in
>       (==)
>         (unifyTypes x y)
>         (Left $ FreeVariableCapture (Var "x1"))

In the final example, we have one bound variable being matched to two others, which fails to unify.

>   , let
>       x = ForAll (S.fromList [Var "x0"])
>         (TArr Q (TVar Q (Var "x0")) (TVar Q (Var "x0")))
>       y = ForAll (S.fromList [Var "x0", Var "x1"])
>         (TArr Q (TVar Q (Var "x1")) (TVar Q (Var "x0")))
>     in
>       (==)
>         (unifyTypes x y)
>         (Left IncompatibleSub)
>   ]

In the next section we will see how to assign types to lambda expressions.
