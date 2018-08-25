---
title: Module
---

We've come a long way. At this point we can formally typecheck and verify natural deduction style proofs using first order logic and a model of simply typed lambda calculus with let bindings. We're nearly prepared to implement a more compact syntax and bundle the checker in a command line tool.

Before we do that, though, let's check some proofs written out the long way in abstract syntax as a test.

As usual we start with imports.

> module Module where
> 
> import Control.Monad.Loops
>   ( concatM )
> import Test.QuickCheck
> 
> import Var
> import Sub
> import Expr
> import Type
> import Infer
> import Jud
> import Proof



Modules
-------

In practice, type definitions, axioms, and theorems will be stored together in text files. We can abstract this idea, multiple claims stored together, as a _module_.

> data Module
>   = Module ModuleName [Claim]
>   deriving (Show)
> 
> instance Eq Module where
>   (Module _ cs) == (Module _ ds) = cs == ds
> 
> instance Arbitrary Module where
>   arbitrary = Module <$> arbitrary <*> arbitrary
> 
>   shrink (Module n m) = map (Module n) $ shrink m

I can imagine a scenario where modules do something more sophisticated, like automatic imports or namespace management. As of this writing, I can't really say what fancy features a module system should have, so we'll defer all that for now. A module is just a list of claims.

> data ModuleName = ModuleName String
>   deriving (Eq, Show)
> 
> instance Arbitrary ModuleName where
>   arbitrary = do
>     n <- listOf1 $ elements _modulename_chars
>     return (ModuleName n)
> 
> _modulename_chars = concat
>   [ "abcdefghijklmnopqrstuvwxyz"
>   , "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
>   , "0123456789-_@/"
>   ]

Now we can check a single module:

> checkModule
>   :: Module -> (TypeEnv, RuleEnv)
>   -> Either VerifyError (TypeEnv, RuleEnv)
> checkModule (Module _ m) env = checkClaims env m

And we can check a list of modules one after another.

> checkModules
>   :: [Module] -> (TypeEnv, RuleEnv)
>   -> Either VerifyError (TypeEnv, RuleEnv)
> checkModules ms env = concatM (map checkModule ms) env



Tests
-----

We've now got enough technology to test our proof checker with some basic theorems. We're stuck using the abstract syntax for now, so it will be ridiculously verbose. But let's try it out.

When using natural deduction we usually start with a small list of assumed inference rules that can be classified as either _introduction rules_ or _elimination rules_. An introduction rule asserts conditions under which a judgement connective can come into being, while an elimination rule asserts when a connective can be eliminated. For instance, the example inference rule at the beginning of this page is the _and-introduction rule_.

$$\begin{array}{ccc}
P &            & Q \\ \hline
  & P \wedge Q &
\end{array}$$

In our notation, the and-introduction rule looks like this.

> ax_and_intro :: Claim
> ax_and_intro = Axiom
>   (RuleName "and-intro") $
>   Rule
>     (JConj Q (JVar Q (Var "p")) (JVar Q (Var "q")))
>     [ JVar Q (Var "p")
>     , JVar Q (Var "q")
>     ]

This rule governs when the $\wedge$ symbol can be introduced. There are analogous _and-elimination rules_ for removing a $\wedge$:

$$\begin{array}{c}
 P \wedge Q \\ \hline P
\end{array}
\quad\quad
\begin{array}{c}
 P \wedge Q \\ \hline Q
\end{array}$$

> ax_and_elim_1 :: Claim
> ax_and_elim_1 = Axiom
>   (RuleName "and-elim-1") $
>   Rule
>     (JVar Q (Var "p"))
>     [ JConj Q (JVar Q (Var "p")) (JVar Q (Var "q"))
>     ]
> 
> ax_and_elim_2 :: Claim
> ax_and_elim_2 = Axiom
>   (RuleName "and-elim-2") $
>   Rule
>     (JVar Q (Var "q"))
>     [ JConj Q (JVar Q (Var "p")) (JVar Q (Var "q"))
>     ]

And from these we can already prove a theorem:

$$\begin{array}{c}
 P \wedge Q \\ \hline Q \wedge P
\end{array}$$

If we handwrote the proof for this claim, it would look something like this:

$$\begin{array}{ccc}
\begin{array}{c} P \wedge Q \\ \hline Q \end{array}
 & & \begin{array}{c} P \wedge Q \\ \hline P \end{array} \\ \hline
 & Q \wedge P
\end{array}$$

> thm_and_comm :: Claim
> thm_and_comm = Theorem
>   (RuleName "and-comm")
>   (Rule
>     (JConj Q (JVar Q (Var "q")) (JVar Q (Var "p")))
>     [JConj Q (JVar Q (Var "p")) (JVar Q (Var "q"))
>     ])
>   (Use Q (RuleName "and-intro")
>       (JConj Q (JVar Q (Var "q")) (JVar Q (Var "p")))
>     [ Use Q (RuleName "and-elim-2") (JVar Q (Var "q"))
>       [ Assume Q 1 (JConj Q (JVar Q (Var "p")) (JVar Q (Var "q")))
>       ]
>     , Use Q (RuleName "and-elim-1") (JVar Q (Var "p"))
>       [ Assume Q 1 (JConj Q (JVar Q (Var "p")) (JVar Q (Var "q")))
>       ]
>     ])

This notation is tedious! Eventually we will develop a better concrete syntax. For now it's better to work with the raw abstract syntax, to be sure that what we say is what we mean.

We need modus ponens, the $\Rightarrow$-elimination rule.

$$\begin{array}{c}
 P &  & P \Rightarrow Q \\ \hline
 & Q &
\end{array}$$

> ax_modus_ponens :: Claim
> ax_modus_ponens = Axiom
>   (RuleName "modus-ponens") $
>   Rule
>     (JVar Q (Var "q"))
>     [ JVar Q (Var "p")
>     , JImpl Q (JVar Q (Var "p")) (JVar Q (Var "q"))
>     ]

We can now show that $\Rightarrow$ is transitive.

> thm_imp_trans :: Claim
> thm_imp_trans = Theorem
>   (RuleName "imp-trans")
>   (Rule
>     ( JImpl Q (JVar Q (Var "p")) (JVar Q (Var "r")) )
>     [ JImpl Q (JVar Q (Var "p")) (JVar Q (Var "q"))
>     , JImpl Q (JVar Q (Var "q")) (JVar Q (Var "r"))
>     ])
>   (Dis Q (HypName "assume-p")
>       (JImpl Q (JVar Q (Var "p")) (JVar Q (Var "r"))) $
>     Use Q (RuleName "modus-ponens")
>     (JVar Q (Var "r"))
>     [ Use Q (RuleName "modus-ponens")
>       (JVar Q (Var "q"))
>       [ Hyp Q (HypName "assume-p")
>         (JVar Q (Var "p"))
>       , Assume Q 1 (JImpl Q (JVar Q (Var "p")) (JVar Q (Var "q")))
>       ]
>     , Assume Q 2 (JImpl Q (JVar Q (Var "q")) (JVar Q (Var "r")))])

Next we'll test substitution proofs. We need an introduction rule for equality:

$$\begin{array}{c}
 \\ \hline x = x
\end{array}$$

> ax_eq_intro :: Claim
> ax_eq_intro = Axiom
>   (RuleName "eq-intro") $
>   Rule
>     (JEq Q (EVar Q (Var "x")) (EVar Q (Var "x")))
>     []

And we can prove that equality is symmetric.

> thm_eq_sym :: Claim
> thm_eq_sym = Theorem
>   (RuleName "eq-sym")
>   (Rule
>     (JEq Q (EVar Q (Var "y")) (EVar Q (Var "x")))
>     [JEq Q (EVar Q (Var "x")) (EVar Q (Var "y"))])
>   (ElimEq Q (JEq Q (EVar Q (Var "y")) (EVar Q (Var "x")))
>       (Var "z") (JEq Q (EVar Q (Var "z")) (EVar Q (Var "x")))
>     (Assume Q 1 (JEq Q (EVar Q (Var "x")) (EVar Q (Var "y"))))
>     (Use Q (RuleName "eq-intro")
>       (JEq Q (EVar Q (Var "x")) (EVar Q (Var "x")))
>       []))

We can put all of these claims together in a module and check them for validity.

> test_toy_theory :: Bool
> test_toy_theory =
>   let
>     claims =
>       [ ax_and_intro
>       , ax_and_elim_1
>       , ax_and_elim_2
>       , thm_and_comm
>       , ax_modus_ponens
>       , thm_imp_trans
>       , ax_eq_intro
>       , thm_eq_sym
>       ]
> 
>     m = Module (ModuleName "module") claims
>   in
>     case checkModule m (emptyTypeEnv, RuleEnv mempty) of
>       Left err -> error $ show err
>       Right _ -> True
