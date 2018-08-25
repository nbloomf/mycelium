---
title: Infer
---

We're now prepared to infer the most general type of a lambda expression.

For instance, the expression $$\lambda\ x\ . x$$ accepts a value of any type, and just returns the value. It's reasonable to say it should have type $$\forall \alpha\ .\ \alpha \rightarrow \alpha.$$

We will implement an algorithm that can automatically determine the type of an expression, or determine that the expression cannot be typed for one of a small number of reasons.

As usual we start with module imports.

> {-# LANGUAGE LambdaCase #-}
> module Infer where
>
> import Control.Monad
>   ( ap, foldM )
> import Data.Either
>   ( rights, lefts )
> import qualified Data.Map as M
>   ( Map(..), fromSet, lookup, keys, fromList
>   , insert, empty, map, elems, delete, toAscList )
> import Data.Proxy
>   ( Proxy(..) )
> import qualified Data.Set as S
>   ( Set(..), empty, fromList, difference
>   , unions, singleton, union )
> import Test.QuickCheck
>   ( Arbitrary(..), Property, Gen, forAll
>   , elements, getSize )
>
> import Var
> import Expr
> import Sub
> import Type



Type Environments
-----------------

Type inference will only make sense in the context of an _environment_ in which some constants and free expression variables have been assigned types.

A _type environment_ is a mapping from expression constants and variables to polytypes. We can think of an environment as a context within which some constants and variables have already been assigned types.

> data TypeEnv =
>   TypeEnv (M.Map (Either (Con Expr) (Var Expr)) PolyType)
>   deriving (Eq, Show)
> 
> instance Arbitrary TypeEnv where
>   arbitrary = TypeEnv <$> arbitrary
> 
>   shrink (TypeEnv m) = map TypeEnv $ shrink m

A variable is free in a type environment if it is free in some image.

> instance FreeTypeVars TypeEnv where
>   freeTypeVars (TypeEnv m) =
>     S.unions $ map freeTypeVars $ M.elems m

And we can apply a monotype substitution to a type environment "pointwise".

> instance SubMono TypeEnv where
>   s $. (TypeEnv m) =
>     TypeEnv $ M.map (s $.) m

We can also unify type environments; in practice this is used just for testing.

> instance UnifyTypes TypeEnv where
>   unifyTypes (TypeEnv m1) (TypeEnv m2) = do
>     let
>       as1 = M.toAscList m1
>       as2 = M.toAscList m2
> 
>       unify (x1,t1) (x2,t2) = if x1 == x2
>         then unifyTypes t1 t2
>         else Left $ IncompatibleSub
> 
>       zipL = \case
>         (y:ys,z:zs) -> do
>           u <- unify y z
>           (u:) <$> zipL (ys,zs)
>         ([],[]) -> return []
>         _ -> Left $ IncompatibleSub
> 
>     us <- zipL (as1,as2)
>     return $ mconcat us

Inference will start out with an empty type environment and be extended or restricted one definition at a time.

> emptyTypeEnv :: TypeEnv
> emptyTypeEnv = TypeEnv M.empty
>
> setTypeOfVar :: TypeEnv -> (Var Expr, PolyType) -> TypeEnv
> setTypeOfVar (TypeEnv env) (var, polytype) =
>   TypeEnv $ M.insert (Right var) polytype env
> 
> removeTypeOfVar :: Var Expr -> TypeEnv -> TypeEnv
> removeTypeOfVar x (TypeEnv m) =
>   TypeEnv $ M.delete (Right x) m
>
> setTypeOfCon :: TypeEnv -> (Con Expr, PolyType) -> TypeEnv
> setTypeOfCon (TypeEnv env) (con, polytype) =
>   TypeEnv $ M.insert (Left con) polytype env

We'll also need to extract the sets of defined variables in a type environment.

> typedVarsIn :: TypeEnv -> S.Set (Var Expr)
> typedVarsIn (TypeEnv env) = S.fromList $ rights $ M.keys env



The Infer Monad
---------------

Inference will happen in a basic monad stack with error and state; error for signaling why an expression fails to typecheck, and state for maintaining a source of fresh type variables.

> data Infer a = Infer
>   { runInfer
>       :: Integer
>       -> Either
>         (Either UnificationError TypeError)
>         (a, Integer)
>   }

Type inference can fail for one of three reasons: (1) we encounter a constant or variable that is not assigned a type in the environment, (2) two expressions which should have the same type, don't, and (3) two types that should unify, don't.

> data TypeError
>   = UnknownVariable Loc (Var Expr)
>   | UnknownConstant Loc (Con Expr)
>   | TypeMismatch Expr MonoType Expr MonoType
>   deriving (Eq, Show)

The monad instance for `Infer` is standard stuff. We could use a monad transformer library for this but I don't want to.

> instance Monad Infer where
>   return a = Infer $ \k -> Right (a, k)
> 
>   x >>= f = Infer $ \k1 ->
>     case runInfer x k1 of
>       Left err -> Left err
>       Right (a,k2) -> runInfer (f a) k2
> 
> instance Applicative Infer where
>   pure = return
>   (<*>) = ap
> 
> instance Functor Infer where
>   fmap f x = x >>= (return . f)

We need utilities for throwing errors:

> throwT :: TypeError -> Infer a
> throwT err = Infer $ \_ -> Left (Right err)
>
> throwU :: UnificationError -> Infer a
> throwU err = Infer $ \_ -> Left (Left err)

And utilities for looking up the value of a variable or constant in the type environment.

> lookupEnvVar :: Loc -> TypeEnv -> Var Expr -> Infer PolyType
> lookupEnvVar loc (TypeEnv m) x = case M.lookup (Right x) m of
>   Nothing -> throwT $ UnknownVariable loc x
>   Just e  -> return e
>
> lookupEnvCon :: Loc -> TypeEnv -> Con Expr -> Infer PolyType
> lookupEnvCon loc (TypeEnv m) c = case M.lookup (Left c) m of
>   Nothing -> throwT $ UnknownConstant loc c
>   Just e  -> return e

We need a utility for generating a fresh type variable.

> freshTypeVar :: Infer MonoType
> freshTypeVar = Infer $ \k ->
>   Right (TVar Q $ Var $ 'w' : show k, k+1)

Finally, we'll use a helper for running computations in `Infer` for convenience.

> execInfer
>   :: Infer a
>   -> Either (Either UnificationError TypeError) a
> execInfer x = case runInfer x 0 of
>   Right (a,_) -> Right a
>   Left err -> Left err



Inference
---------

Almost there! We need two more utility functions on types before we can implement the inference algorithm, which are sort of opposites of each other. Remember that we have two different kinds of types: monotypes and polytypes.

A monotype can be _generalized_ by explicitly quantifying any of its variables that are not free in a given environment.

> generalize :: TypeEnv -> MonoType -> PolyType
> generalize env tau = ForAll as tau
>   where
>     as = S.difference (freeTypeVars tau) (freeTypeVars env)

And a polytype can be _instantiated_ by replacing its bound variables with fresh type variable names.

> instantiate :: PolyType -> Infer MonoType
> instantiate (ForAll as t) = do
>   sub <- freshen as
>   return (sub $. t)
> 
>   where
>     freshen :: S.Set (Var MonoType) -> Infer (Sub MonoType)
>     freshen xs = do
>        m <- sequence $ M.fromSet (const freshTypeVar) xs
>        return (Sub m)

Now we can infer the type of an expression. The `infer` function takes a type environment and an expression, and if it succeeds, returns a monotype and a type substitution to be applied to the environment.

> infer :: TypeEnv -> Expr -> Infer (Sub MonoType, MonoType)
> infer env = \case
>   ECon loc c -> do
>     tau <- lookupEnvCon loc env c >>= instantiate
>     return (mempty, tau)
> 
>   EVar loc x -> do
>     tau <- lookupEnvVar loc env x >>= instantiate
>     return (mempty, tau)

Inferring types for constants and variables is similar; we try to look them up in the type environment and instantiate. In both cases the substitution is empty.

>   ELam loc x e -> do
>     tau <- freshTypeVar
>     let
>       sigma = ForAll S.empty tau
>       env' = setTypeOfVar env (x, sigma)
>     (s, tau') <- infer env' e
>     return (s, TArr loc (s $. tau) tau')

To infer the type of a lambda expression, we introduce a fresh type variable for the dummy variable and add it to the type environment. We then infer the type of the subexpression, with the newly typed dummy variable.

>   ELet _ x e1 e2 -> do
>     (s1, tau) <- infer env e1
>     let
>       env' = s1 $. env
>       sigma = generalize env' tau
>       env'' = setTypeOfVar env' (x, sigma)
>     (s2, tau') <- infer env'' e2
>     return (s2 <> s1, tau')

For a let expression, we first infer the type of the let bound expression in the initial environment. We generalize this type and extend the type environment at the dummy variable.

>   EApp loc f x -> do
>     (s1, fTau) <- infer env f
>     (s2, xTau) <- infer (s1 $. env) x
>     fxTau <- freshTypeVar
>     case unifyTypes (s2 $. fTau) (TArr loc xTau fxTau) of
>       Left err -> throwU err
>       Right s3 ->
>         return (s3 <> s2 <> s1, s3 $. fxTau)

Given an application expression, we essentially infer the types of each branch and unify.

This is a good time for some test cases.

> test_cases_infer :: Bool
> test_cases_infer = 
>   let
>     check e t =
>       case execInfer (infer emptyTypeEnv e) of
>         Left _ -> False
>         Right (_,u) -> (==)
>           (generalize emptyTypeEnv t)
>           (generalize emptyTypeEnv u)
>   in and
>     [ check
>         (ELam Q (Var "x") (EVar Q (Var "x")))
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "a")))
> 
>     , check
>         (ELet Q (Var "x")
>           (ELam Q (Var "y") (EVar Q (Var "y")))
>           (ELam Q (Var "z")
>             (EApp Q (EVar Q (Var "z")) (EVar Q (Var "x")))))
>         (TArr Q
>           (TArr Q
>             (TArr Q (TVar Q (Var "a")) (TVar Q (Var "a")))
>             (TVar Q (Var "b")))
>           (TVar Q (Var "b")))
>     ]

Naively generating arbitrary test cases for type inference is problematic; to meaningfully test expressions with free variables and constants we need to have an appropriate type environment first. The naive way to generate a type environment ends up giving us lots of malformed and unnatural type environments. A realistic environment will have been built up one step at a time, with each new type definition coming from a typeable expression and being consistent with the ones before.

To get more meaningful test results, we need a specialized test case generator for `TypeEnv`s; one that builds up an environment one typed expression at a time.

> genTypeEnv :: Gen TypeEnv
> genTypeEnv = do
>   k <- getSize
>   genEnv k
> 
>   where
>     genEnv :: Int -> Gen TypeEnv
>     genEnv k =
>       if k <= 0
>         then return emptyTypeEnv
>         else do
>           m <- elements [0..(k-1)]
>           genEnv m >>= extend
> 
>     extend :: TypeEnv -> Gen TypeEnv
>     extend env = do
>       let x = fresh [ typedVarsIn env ]
>       e <- arbitrary
>       case execInfer $ infer env e of
>         Right (_,t) -> return $
>           setTypeOfVar env (x, generalize env t)
>         Left _ -> extend env

With this generator in hand, we can define a property test.

> test_infer_sub :: Expr -> Property
> test_infer_sub e = forAll genTypeEnv (test_infer_sub' e)
>   where
>   test_infer_sub' :: Expr -> TypeEnv -> Bool
>   test_infer_sub' e env = case execInfer $ infer env e of 
>     Left _ -> True
>     Right (s,t1) -> case execInfer $ infer (s $. env) e of
>       Left _ -> False
>       Right (_,t2) -> (==)
>         (generalize env (s $. t1))
>         (generalize env t2)



Type Checking
-------------

The main thing we do with type inference is make sure that a given expression can be assigned a type. We'll call this _type checking_. This process will take a possibly typeable thing and a type environment, and attempt to construct a new environment within which the possibly typeable thing has a type. We can wrap this in a class.

> class (HasExprVars t) => TypeCheck t where
>   typeCheck :: t -> TypeEnv -> Infer TypeEnv

In the process of type checking, we will often need to introduce or eliminate variables in type environments.

> introTypeVar :: Var Expr -> TypeEnv -> Infer TypeEnv
> introTypeVar x env = do
>   tau <- freshTypeVar
>   return $ setTypeOfVar env (x, ForAll S.empty tau)
> 
> introTypeVars
>   :: (Foldable f) => f (Var Expr) -> TypeEnv -> Infer TypeEnv
> introTypeVars xs env = foldM (flip introTypeVar) env xs
> 
> elimTypeVar :: Var Expr -> TypeEnv -> Infer TypeEnv
> elimTypeVar x env =
>  return $ removeTypeOfVar x env

Now `Expr`s can be type checked. To do this we first introduce a new type variable for each free expression variable and then infer the type of the expression.

> instance TypeCheck Expr where
>   typeCheck e env = do
>     env' <- introTypeVars (freeExprVars e) env
>     (s,_) <- infer env' e
>     return $ s $. env'

Let's see some examples. First we need a helper; it will be more useful to check type environments "up to a unification". `_typecheck_and_unify` takes care of this.

> _typecheck_and_unify
>   :: (TypeCheck t) => t -> TypeEnv -> Bool
> _typecheck_and_unify a env =
>   let x = execInfer $ typeCheck a emptyTypeEnv in
>   case x of
>     Right ex -> case unifyTypes ex env of
>       Left _ -> False
>       Right s -> trivialMonoTypeSub s
>     Left _ -> True

And the test cases. First: from $\lambda x . y x$ we infer that $y$ has type $a \rightarrow b$ for some types $a$ and $b$.

> test_cases_typecheck_expr :: Bool
> test_cases_typecheck_expr = and
>   [ _typecheck_and_unify
> 
>     (ELam Q (Var "x")
>       (EApp Q (EVar Q (Var "y")) (EVar Q (Var "x"))))
> 
>     (TypeEnv $ M.fromList
>       [ (Right (Var "y"), ForAll (S.fromList [])
>         (TArr Q (TVar Q (Var "a")) (TVar Q (Var "b"))))
>       ])

From $\lambda x . \lambda y . (zx)y$ we infer that $z$ has type $a \rightarrow b \rightarrow c$.

>   , _typecheck_and_unify
> 
>     (ELam Q (Var "x")
>       (ELam Q (Var "y")
>         (EApp Q
>           (EApp Q (EVar Q (Var "z")) (EVar Q (Var "x")))
>           (EVar Q (Var "y")))))
> 
>     (TypeEnv $ M.fromList
>       [ (Right (Var "z"), ForAll (S.fromList [])
>         (TArr Q (TVar Q (Var "a"))
>           (TArr Q (TVar Q (Var "b")) (TVar Q (Var "c")))))
>       ])
>   ]

Type checking is important, so we should think about property testing for it. Since `TypeCheck` is a subclass of `HasExprVars`, we should think about how `typeCheck` interacts with the renaming functions.

For instance: the free variables in a type checked thing are assigned types in the environment.

> test_typecheck_free_vars
>   :: (TypeCheck t) => Proxy t -> t -> Property
> test_typecheck_free_vars _ x =
>   forAll genTypeEnv (test_typecheck_free_vars' x)
>   where
>     test_typecheck_free_vars'
>       :: (TypeCheck t) => t -> TypeEnv -> Bool
>     test_typecheck_free_vars' x env =
>       case execInfer $ typeCheck x env of
>         Left _ -> True
>         Right (TypeEnv m) ->
>           all (\z -> elem (Right z) $ M.keys m) (freeExprVars x)

Another property is that renaming the bound variables in a type checkable thing should not affect the outcome of type checking.

> test_typecheck_bound_vars
>   :: (TypeCheck t) => Proxy t -> t -> S.Set (Var Expr) -> Property
> test_typecheck_bound_vars _ x avoid =
>   forAll genTypeEnv (test_typecheck_bound_vars' x avoid)
>   where
>     test_typecheck_bound_vars'
>       :: (TypeCheck t) => t -> S.Set (Var Expr) -> TypeEnv -> Bool
>     test_typecheck_bound_vars' x avoid env =
>       let
>         a = execInfer $ typeCheck x env
>         b = execInfer $ typeCheck
>           (renameBoundExpr
>             (S.unions [avoid, typedVarsIn env, freeExprVars x]) x) env
>       in case (a,b) of
>         (Right env1, Right env2) -> case unifyTypes env1 env2 of
>           Left _ -> False
>           Right s -> True
>         (Left _, Left _) -> True
>         _ -> False

And renaming free variables is reflected in the type check result.

> test_typecheck_rename_free
>   :: (TypeCheck t) => Proxy t -> t -> Property
> test_typecheck_rename_free _ t =
>   forAll genTypeEnv (test_typecheck_rename_free' t)
>   where
>     test_typecheck_rename_free'
>       :: (TypeCheck t) => t -> TypeEnv -> Bool
>     test_typecheck_rename_free' t env =
>       let
>         x = fresh
>           [ typedVarsIn env ]
>         y = fresh
>           [ S.singleton x
>           , freeExprVars t
>           , typedVarsIn env ]
>         a = execInfer $ do
>           env' <- typeCheck t env
>           lookupEnvVar Q env' x
>         b = execInfer $ do
>           env' <- typeCheck (renameFreeExpr (x,y) t) env
>           lookupEnvVar Q env' y
>       in
>         case (a,b) of
>           (Right e1, Right e2) -> case unifyTypes e1 e2 of
>             Left _ -> False
>             Right s -> True
>           (Left _, Left _) -> True
>           _ -> False



Recap
-----

We've defined a grammar of types and developed a function for inferring the type of a lambda expression.

In the next sections we'll use lambda expressions as the basis for a grammar of logical statements.
