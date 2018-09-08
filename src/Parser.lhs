---
title: Parser
---

We're finally ready to define a more compact syntax for proofs. Woo! We'll use the [parsec](http://hackage.haskell.org/package/parsec) library for this.

As usual we start with some imports.

> {-# LANGUAGE FlexibleInstances, FlexibleContexts, LambdaCase #-}
> module Parser where
> 
> import Data.List
>   ( unwords, intercalate )
> import qualified Data.Map as M
> import Data.Proxy
>   ( Proxy(..) )
> import qualified Data.Set as S
> import Text.ParserCombinators.Parsec
> import Text.ParserCombinators.Parsec.Expr
> 
> import Var
> import Sub
> import Expr
> import Type
> import Jud
> import Proof
> import Module
> import Fancy



Basics
------

We're going to provide two different syntaxes for proofs: the basic tree-formatted style, and the serialized fancy style. The difference between the two is only important when parsing proofs (not expressions). We can wrap both of these behind a class to make testing simpler.

> class PrettyBasic t where
>   prettyBasic :: t -> String
> 
>   prettyBasicWrap :: t -> String
>   prettyBasicWrap t =
>     let m = prettyBasic t in
>     if (elem ' ' m) || (elem '.' m) || (elem '~' m)
>       then "(" ++ m ++ ")"
>       else m
> 
>   parseBasic :: Parser t

The `prettyBasicWrap` function inserts parentheses where the syntax might otherwise be ambiguous.

> class PrettyFancy t where
>   prettyFancy :: t -> String
> 
>   parseFancy :: Parser t

We also need some parsing helpers. First a utility to get the `Loc`ation of the current character in the text.

> getLoc :: Parser Loc
> getLoc = do
>   pos <- getPosition
>   return $ Loc (sourceName pos) (sourceLine pos) (sourceColumn pos)

We'll also be tossing out lots of whitespace. But the `spaces` parser built into parsec eats newlines, which we want to avoid. `spaceChars` parses only spaces.

> spaceChars :: Parser ()
> spaceChars = many (char ' ') >> return ()
> 
> spaceOrNewlines :: Parser ()
> spaceOrNewlines = many (oneOf " \n") >> return ()

The next two are for wrapping a parser in parentheses or curly braces.

> parens :: Parser a -> Parser a
> parens p = between (char '(' >> spaceChars) (char ')' >> spaceChars) p
> 
> braces :: Parser a -> Parser a
> braces p = between (char '{' >> spaceChars) (char '}' >> spaceChars) p

We also want to test our parsers extensively. We can do this by hand with `testBasicParser` and `testFancyParser`.

> testBasicParser
>   :: (PrettyBasic t, Eq t)
>   => Proxy t -> String -> Either String t -> Bool
> testBasicParser _ str expected =
>   case runParser parseBasic () "" str of
>     Left err -> expected == Left (show err)
>     Right x -> expected == Right x
> 
> testFancyParser
>   :: (PrettyFancy t, Eq t)
>   => Proxy t -> String -> Either String t -> Bool
> testFancyParser _ str expected =
>   case runParser parseFancy () "" str of
>     Left err -> expected == Left (show err)
>     Right x -> expected == Right x

As a property test, we can verify that the pretty/parse round trip is the identity.

> test_prettybasic
>   :: (PrettyBasic t, Eq t) => Proxy t -> t -> Bool
> test_prettybasic _ t =
>   case runParser parseBasic () "" (prettyBasic t) of
>     Left err -> error $ show err
>     Right u -> t == u
> 
> test_prettyfancy
>   :: (PrettyFancy t, Eq t) => Proxy t -> t -> Bool
> test_prettyfancy _ t =
>   case runParser parseFancy () "" (prettyFancy t) of
>     Left err -> error $ show err
>     Right u -> t == u



Expressions
-----------

Expression variables start with a lowercase latin character, followed by 0 or mor latin characters, followed by 0 or more digits.

> instance PrettyBasic (Var Expr) where
>   prettyBasic (Var s) = s
> 
>   parseBasic = do
>     a <- oneOf _latin_lc
>     as <- many $ oneOf _latin
>     bs <- many $ oneOf _digit
>     spaceChars
>     return (Var $ a:as ++ bs)
> 
> _latin_lc = "abcdefghijklmnopqrstuvwxyz"
> 
> _latin = concat
>   [ "abcdefghijklmnopqrstuvwxyz"
>   , "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
>   ]
> 
> _digit = "0123456789"

Test cases:

> test_cases_parse_varexpr :: Bool
> test_cases_parse_varexpr = and
>   [ testBasicParser (Proxy :: Proxy (Var Expr))
>       "x" (Right $ Var "x")
>   , testBasicParser (Proxy :: Proxy (Var Expr))
>       "x0" (Right $ Var "x0")
>   , testBasicParser (Proxy :: Proxy (Var Expr))
>       "xA0" (Right $ Var "xA0")
>   , testBasicParser (Proxy :: Proxy (Var Expr))
>       "xa0" (Right $ Var "xa0")
>   ]

Expression constants are the same as variables, but start with a backslash.

> instance PrettyBasic (Con Expr) where
>   prettyBasic (Con s) = '\\' : s
> 
>   parseBasic = do
>     char '\\'
>     a <- oneOf _latin_lc
>     as <- many $ oneOf _latin
>     bs <- many $ oneOf _digit
>     spaceChars
>     return (Con $ a:as ++ bs)

Test cases:

> test_cases_parse_conexpr :: Bool
> test_cases_parse_conexpr = and
>   [ testBasicParser (Proxy :: Proxy (Con Expr))
>       "\\x" (Right $ Con "x")
>   , testBasicParser (Proxy :: Proxy (Con Expr))
>       "\\x0" (Right $ Con "x0")
>   , testBasicParser (Proxy :: Proxy (Con Expr))
>       "\\xA0" (Right $ Con "xA0")
>   , testBasicParser (Proxy :: Proxy (Con Expr))
>       "\\xa0" (Right $ Con "xa0")
>   ]

Now for lambda expressions.

> instance PrettyBasic Expr where
>   prettyBasic = \case
>     ECon _ c ->
>       prettyBasic c
>     EVar _ x ->
>       prettyBasic x
>     ELam _ x e -> concat
>       [ "λ", prettyBasic x, ".", prettyBasicWrap e ]
>     ELet _ x f g -> unwords
>       [ "'let", prettyBasic x
>       , "=", prettyBasicWrap f
>       , "'in", prettyBasicWrap g
>       ]
>     EApp _ e f ->
>       prettyBasicWrap e ++ " " ++ prettyBasicWrap f
> 
>   parseBasic =
>     chainl1 parseForm (do { loc <- getLoc; return (EApp loc) })
>     where
>       parseForm =
>         parseLam <|> parseLet <|> parseCon
>           <|> parseVar <|> fenced parseBasic
> 
>       parseLam = do
>         loc <- try $ getLoc <* (char 'λ' >> spaceChars)
>         x <- parseBasic
>         spaceChars >> char '.' >> spaceChars
>         e <- parseBasic
>         return $ ELam loc x e
> 
>       parseLet = do
>         loc <- try $ getLoc <* (string "'let" >> spaceChars)
>         x <- parseBasic
>         char '=' >> spaceChars
>         e1 <- parseBasic
>         string "'in" >> spaceChars
>         e2 <- parseBasic
>         return $ ELet loc x e1 e2
> 
>       parseCon = do
>         loc <- getLoc
>         c <- try parseBasic
>         return (ECon loc c)
> 
>       parseVar = do
>         loc <- getLoc
>         x <- try parseBasic
>         return (EVar loc x)
> 
>       fenced p = parens p <|> braces p

Application is left associative, so that $x y z$ parses as $(xy)z$.

Test cases:

> test_cases_parse_expr :: Bool
> test_cases_parse_expr = and
>   [ testBasicParser (Proxy :: Proxy Expr)
>       "x"
>       (Right $ EVar Q (Var "x"))
> 
>   , testBasicParser (Proxy :: Proxy Expr)
>       "x y"
>       (Right $ EApp Q (EVar Q (Var "x")) (EVar Q (Var "y")))
> 
>   , testBasicParser (Proxy :: Proxy Expr)
>       "x y z"
>       (Right $ EApp Q
>         (EApp Q (EVar Q (Var "x")) (EVar Q (Var "y")))
>         (EVar Q (Var "z")))
> 
>   , testBasicParser (Proxy :: Proxy Expr)
>       "x (y z)"
>       (Right $ EApp Q
>         (EVar Q (Var "x"))
>         (EApp Q (EVar Q (Var "y")) (EVar Q (Var "z"))))
> 
>   , testBasicParser (Proxy :: Proxy Expr)
>       "λx.x"
>       (Right $ ELam Q (Var "x") (EVar Q (Var "x")))
> 
>   , testBasicParser (Proxy :: Proxy Expr)
>       "'let x = \\c 'in x"
>       (Right $ ELet Q (Var "x") (ECon Q (Con "c")) (EVar Q (Var "x")))
>   ]



Types
-----

Type variables look like expression variables.

> instance PrettyBasic (Var MonoType) where
>   prettyBasic (Var s) = s
> 
>   parseBasic = do
>     a <- oneOf _latin_lc
>     as <- many $ oneOf _latin
>     bs <- many $ oneOf _digit
>     spaceChars
>     return (Var $ a:as ++ bs)

Test cases:

> test_cases_parse_varmonotype :: Bool
> test_cases_parse_varmonotype = and
>   [ testBasicParser (Proxy :: Proxy (Var MonoType))
>       "x" (Right $ Var "x")
>   , testBasicParser (Proxy :: Proxy (Var MonoType))
>       "x0" (Right $ Var "x0")
>   , testBasicParser (Proxy :: Proxy (Var MonoType))
>       "xA0" (Right $ Var "xA0")
>   , testBasicParser (Proxy :: Proxy (Var MonoType))
>       "xa0" (Right $ Var "xa0")
>   ]

Type constants are like type variables, but must start with an upper case latin character.

> instance PrettyBasic (Con MonoType) where
>   prettyBasic (Con s) = s
> 
>   parseBasic = do
>     a <- oneOf _latin_uc
>     as <- many $ oneOf _latin
>     bs <- many $ oneOf _digit
>     spaceChars
>     return (Con $ a:as ++ bs)
> 
> _latin_uc = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

Test cases:

> test_cases_parse_conmonotype :: Bool
> test_cases_parse_conmonotype = and
>   [ testBasicParser (Proxy :: Proxy (Con MonoType))
>       "X" (Right $ Con "X")
>   , testBasicParser (Proxy :: Proxy (Con MonoType))
>       "X0" (Right $ Con "X0")
>   , testBasicParser (Proxy :: Proxy (Con MonoType))
>       "XA0" (Right $ Con "XA0")
>   , testBasicParser (Proxy :: Proxy (Con MonoType))
>       "Xa0" (Right $ Con "Xa0")
>   ]

Now for the grammar of monotypes.

> instance PrettyBasic MonoType where
>   prettyBasic = \case
>     TCon _ c -> prettyBasic c
>     TVar _ x -> prettyBasic x
>     TArr _ a b -> unwords
>       [ prettyBasicWrap a
>       , "->"
>       , prettyBasic b
>       ]
>     TSt1 _ c a -> unwords
>       [ prettyBasic c
>       , prettyBasicWrap a
>       ]
>     TSt2 _ c a b -> unwords
>       [ prettyBasic c
>       , prettyBasicWrap a
>       , prettyBasicWrap b
>       ]
> 
>   parseBasic = chainr1 (parseF <|> parseForm) parseArr
>     where
>       parseForm = parseCon <|> parseVar <|> parens parseBasic
> 
>       parseF = do
>         loc <- getLoc
>         c <- try parseBasic
>         option (TCon loc c) $ do
>           x <- parseForm
>           option (TSt1 loc c x) $ do
>             y <- parseForm
>             return $ TSt2 loc c x y
> 
>       parseArr = do
>         loc <- getLoc
>         string "->"
>         spaceChars
>         return (TArr loc)
> 
>       parseCon = do
>         loc <- getLoc
>         c <- try parseBasic
>         return (TCon loc c)
> 
>       parseVar = do
>         loc <- getLoc
>         x <- try parseBasic
>         return (TVar loc x)

Note that the arrow type is right associative, so that $a \rightarrow b \rightarrow c$ parses as $a \rightarrow (b \rightarrow c)$.

Test cases:

> test_cases_parse_monotype :: Bool
> test_cases_parse_monotype = and
>   [ testBasicParser (Proxy :: Proxy MonoType)
>       "x"
>       (Right $ TVar Q (Var "x"))
> 
>   , testBasicParser (Proxy :: Proxy MonoType)
>       "x -> y"
>       (Right $ TArr Q (TVar Q (Var "x")) (TVar Q (Var "y")))
> 
>   , testBasicParser (Proxy :: Proxy MonoType)
>       "x -> y -> z"
>       (Right $ TArr Q
>         (TVar Q (Var "x"))
>         (TArr Q (TVar Q (Var "y")) (TVar Q (Var "z"))))
> 
>   , testBasicParser (Proxy :: Proxy MonoType)
>       "(x -> y) -> z"
>       (Right $ TArr Q
>         (TArr Q (TVar Q (Var "x")) (TVar Q (Var "y")))
>         (TVar Q (Var "z")))
> 
>   , testBasicParser (Proxy :: Proxy MonoType)
>       "C"
>       (Right $ TCon Q (Con "C"))
> 
>   , testBasicParser (Proxy :: Proxy MonoType)
>       "C x"
>       (Right $ TSt1 Q (Con "C") (TVar Q (Var "x")))
> 
>   , testBasicParser (Proxy :: Proxy MonoType)
>       "C x y"
>       (Right $ TSt2 Q (Con "C") (TVar Q (Var "x")) (TVar Q (Var "y")))
>   ]

And polytypes.

> instance PrettyBasic PolyType where
>   prettyBasic (ForAll as tau) = unwords
>     [ "∀"
>     , vars
>     , "."
>     , prettyBasic tau
>     ]
>     where
>       vars = if S.null as
>         then "∅"
>         else unwords . map prettyBasic . S.toList $ as
> 
>   parseBasic = do
>     char '∀'
>     spaceChars
>     as <- parseNoVars <|> parseVars
>     char '.' >> spaceChars
>     tau <- parseBasic
>     return $ ForAll as tau
>     where
>       parseNoVars = do
>         try (char '∅' >> spaceChars)
>         return $ S.empty
> 
>       parseVars = do
>         as <- sepBy1 parseBasic spaceChars
>         spaceChars
>         return $ S.fromList as

Test cases:

> test_cases_parse_polytype :: Bool
> test_cases_parse_polytype = and
>   [ testBasicParser (Proxy :: Proxy PolyType)
>       "∀x. x"
>       (Right $ ForAll
>         (S.fromList [Var "x"])
>         (TVar Q (Var "x")))
> 
>   , testBasicParser (Proxy :: Proxy PolyType)
>       "∀x y. x -> y"
>       (Right $ ForAll
>         (S.fromList [Var "x", Var "y"])
>         (TArr Q (TVar Q (Var "x")) (TVar Q (Var "y"))))
> 
>   , testBasicParser (Proxy :: Proxy PolyType)
>       "∀∅. x"
>       (Right $ ForAll
>         (S.fromList [])
>         (TVar Q (Var "x")))
>   ]



Substitutions
-------------

Substitutions will be notated with `:->`, separated by semicolons and wrapped in square brackets.

> instance PrettyBasic (Sub Expr) where
>   prettyBasic (Sub m) =
>     "[" ++ (intercalate "; " $ map f $ M.toList m) ++ "]"
>     where
>       f (x,e) = prettyBasic x ++ " :-> " ++ prettyBasic e
> 
>   parseBasic = do
>     try (char '[' >> spaceChars)
>     as <- sepBy parseSub (char ';' >> spaceChars)
>     char ']' >> spaceChars
>     return $ Sub $ M.fromList as
>     where
>       parseSub = do
>         x <- parseBasic
>         string ":->" >> spaceChars
>         e <- parseBasic
>         return (x,e)

Test cases:

> test_cases_parse_subexpr :: Bool
> test_cases_parse_subexpr = and
>   [ testBasicParser (Proxy :: Proxy (Sub Expr))
>       "[x :-> e]"
>       (Right $ Sub $ M.fromList
>         [ (Var "x", EVar Q (Var "e"))
>         ])
> 
>   , testBasicParser (Proxy :: Proxy (Sub Expr))
>       "[x :-> e; y :-> f g]"
>       (Right $ Sub $ M.fromList
>         [ (Var "x", EVar Q (Var "e"))
>         , (Var "y", EApp Q (EVar Q (Var "f")) (EVar Q (Var "g")))
>         ])
> 
>   , testBasicParser (Proxy :: Proxy (Sub Expr))
>       "[]"
>       (Right $ Sub $ M.fromList [])
>   ]



Judgements
----------

Judgement variables start with an upper case character so they can be easily distinguished from expression variables.

> instance PrettyBasic (Var Jud) where
>   prettyBasic (Var s) = s
> 
>   parseBasic = do
>     a <- oneOf _latin_uc
>     as <- many $ oneOf _latin
>     bs <- many $ oneOf _digit
>     spaceChars
>     return (Var $ a:as ++ bs)

Test cases:

> test_cases_parse_varjud :: Bool
> test_cases_parse_varjud = and
>   [ testBasicParser (Proxy :: Proxy (Var Jud))
>       "X" (Right $ Var "X")
>   , testBasicParser (Proxy :: Proxy (Var Jud))
>       "X0" (Right $ Var "X0")
>   , testBasicParser (Proxy :: Proxy (Var Jud))
>       "XA0" (Right $ Var "XA0")
>   , testBasicParser (Proxy :: Proxy (Var Jud))
>       "Xa0" (Right $ Var "Xa0")
>   ]

The judgement grammar uses infix notation; we use parsec's built in `buildExpressionParser` for this.

> instance PrettyBasic Jud where
>   prettyBasic = \case
>     JVar _ x -> prettyBasic x
>     JNeg _ p -> '~' : prettyBasicWrap p
>     JConj _ p q -> concat
>       [ prettyBasicWrap p, " /\\ ", prettyBasicWrap q ]
>     JDisj _ p q -> concat
>       [ prettyBasicWrap p, " \\/ ", prettyBasicWrap q ]
>     JImpl _ p q -> concat
>       [ prettyBasicWrap p, " => ", prettyBasicWrap q ]
>     JEqui _ p q -> concat
>       [ prettyBasicWrap p, " <=> ", prettyBasicWrap q ]
>     JEq _ e f -> concat
>       [ prettyBasic e, " == ", prettyBasic f ]
>     JIs _ e m -> concat
>       [ prettyBasicWrap e, " 'is ", "\"", m, "\"" ]
>     JAll _ x p -> concat
>       [ "∀", prettyBasic x, ".", prettyBasicWrap p ]
>     JSome _ x p -> concat
>       [ "∃", prettyBasic x, ".", prettyBasicWrap p ]
> 
>   parseBasic = buildExpressionParser ops terms
>     where
>       ops =
>         [ [ Prefix $ do
>             { loc <- getLoc
>             ; string "~" >> spaceChars >> return (JNeg loc)
>             } ]
> 
>         , [ Infix (do
>             { loc <- getLoc
>             ; string "/\\" >> spaceChars >> return (JConj loc)
>             }) AssocNone ]
> 
>         , [ Infix (do
>             { loc <- getLoc
>             ; string "\\/" >> spaceChars >> return (JDisj loc)
>             }) AssocNone ]
> 
>         , [ Infix (do
>             { loc <- getLoc
>             ; string "=>" >> spaceOrNewlines >> return (JImpl loc)
>             }) AssocNone ]
> 
>         , [ Infix (do
>             { loc <- getLoc
>             ; string "<=>" >> spaceChars >> return (JEqui loc)
>             }) AssocNone ]
> 
>         , [ Prefix $ do
>             { loc <- getLoc
>             ; char '∀'; spaceChars
>             ; x <- parseBasic
>             ; char '.' >> spaceChars; return (JAll loc x)
>             } ]
> 
>         , [ Prefix $ do
>             { loc <- getLoc
>             ; char '∃'; spaceChars
>             ; x <- parseBasic
>             ; char '.' >> spaceChars; return (JSome loc x)
>             } ]
>         ]
> 
>       terms = parseVar <|> parseIs <|> parseEq <|> parens parseBasic
>         where
>           parseVar = do
>             loc <- getLoc
>             x <- try parseBasic
>             return (JVar loc x)
> 
>           parseEq = do
>             (e,loc) <- try $ do
>               e' <- parseBasic
>               loc' <- getLoc
>               string "==" >> spaces
>               return (e',loc')
>             f <- parseBasic
>             return (JEq loc e f)
> 
>           parseIs = do
>             (e,loc) <- try $ do
>               e' <- parseBasic
>               loc' <- getLoc
>               string "'is" >> spaceChars
>               return (e',loc')
>             char '"'
>             m <- many1 $ oneOf _is_chars
>             char '"' >> spaceChars
>             return (JIs loc e m)

Test cases:

> test_cases_parse_jud :: Bool
> test_cases_parse_jud = and
>   [ testBasicParser (Proxy :: Proxy Jud)
>       "P" (Right $ JVar Q (Var "P"))
>   , testBasicParser (Proxy :: Proxy Jud)
>       "P /\\ Q" (Right $ JConj Q (JVar Q (Var "P")) (JVar Q (Var "Q")))
>   , testBasicParser (Proxy :: Proxy Jud)
>       "P \\/ Q" (Right $ JDisj Q (JVar Q (Var "P")) (JVar Q (Var "Q")))
>   , testBasicParser (Proxy :: Proxy Jud)
>       "P => Q" (Right $ JImpl Q (JVar Q (Var "P")) (JVar Q (Var "Q")))
>   , testBasicParser (Proxy :: Proxy Jud)
>       "x == y" (Right $ JEq Q (EVar Q (Var "x")) (EVar Q (Var "y")))
>   ]



Names
-----

> instance PrettyBasic HypName where
>   prettyBasic (HypName m) = m
> 
>   parseBasic = do
>     n <-  many1 $ oneOf _hypname_chars
>     spaceChars
>     return $ HypName n
> 
> instance PrettyBasic RuleName where
>   prettyBasic (RuleName m) = m
> 
>   parseBasic = do
>     n <- many1 $ oneOf _rulename_chars
>     spaceChars
>     return $ RuleName n



Rules
-----

We'll accept rules in either basic or fancy style. In basic style, the hypotheses and conclusion are written as an upside-down and indented tree:

```
* conclusion
  * hypothesis 1
  * hypothesis 2
```

In fancy style, the hypotheses come first, and we write out an explicit "if-then":

```
if
  * hypothesis 1
  * hypothesis 2
then
  * conclusion
```

Fancy style is a little more verbose, but easier to read (I think). In both cases indentation is hardcoded at two spaces because that's what I prefer.

First basic style.

> instance PrettyBasic Rule where
>   prettyBasic (Rule q ps) = concat
>     [ "* ", prettyBasic q, "\n" ]
>       ++ (concatMap (\p -> concat ["  * ", prettyBasic p, "\n"]) ps)
> 
>   parseBasic = do
>     try (char '*' >> spaceChars)
>     q <- parseBasic
>     newline
>     ps <- many $ try $ do
>       string "  *" >> spaceChars
>       p <- parseBasic
>       newline
>       return p
>     return (Rule q ps)

Test case:

> test_cases_parse_rule_basic :: Bool
> test_cases_parse_rule_basic = and
>   [ testBasicParser (Proxy :: Proxy Rule)
>       (unlines
>         [ "* P"
>         , "  * Q"
>         ])
>       (Right $ Rule (JVar Q (Var "P")) [JVar Q (Var "Q")])
>   ]

And fancy style:

> instance PrettyFancy Rule where
>   prettyFancy (Rule q ps) =
>     "if\n"
>       ++ (concatMap (\p -> concat ["  * ", prettyBasic p, "\n"]) ps)
>       ++ (concat [ "then\n  * ", prettyBasic q, "\n" ])
> 
>   parseFancy = do
>     try (string "if" >> newline)
>     ps <- many $ try $ do
>       string "  *" >> spaceChars
>       p <- parseBasic
>       newline
>       return p
>     string "then" >> newline
>     string "  *" >> spaceChars
>     p <- parseBasic
>     newline
>     return (Rule p ps)

Test case:

> test_cases_parse_rule_fancy :: Bool
> test_cases_parse_rule_fancy = and
>   [ testFancyParser (Proxy :: Proxy Rule)
>       (unlines
>         [ "if"
>         , "  * Q"
>         , "then"
>         , "  * P"
>         ])
>       (Right $ Rule (JVar Q (Var "P")) [JVar Q (Var "Q")])
>   ]



Proof
-----

Proofs can also be written in either basic or fancy style.

> proofKeyword :: Parser String
> proofKeyword =
>   try (string "assumption") <|>
>   try (string "hypothesis") <|>
>   try (string "discharge") <|>
>   try (string "eq-elim") <|>
>   try (string "eq-intro") <|>
>   try (string "sub") <|>
>   try (string "forall-intro") <|>
>   try (string "forall-elim") <|>
>   try (string "exists-intro") <|>
>   try (string "exists-elim") <|>
>   (string "use")

Basic style:

> instance PrettyBasic Proof where
>   prettyBasic = pretty 0
>     where
>       ind i = replicate (2*i) ' '
> 
>       pretty i = \case
>         Assume _ k p -> concat
>           [ ind i, "* ", prettyBasic p, " : assumption "
>           , show k, "\n" ]
>         Hyp _ name p -> concat
>           [ ind i, "* ", prettyBasic p, " : hypothesis "
>           , prettyBasic name, "\n" ]
>         Dis _ name w pf -> concat
>           [ ind i, "* ", prettyBasic w, " : discharge "
>           , prettyBasic name, "\n" ]
>             ++ pretty (i+1) pf
>         ElimEq _ w x q pe pf -> concat
>           [ ind i, "* ", prettyBasic w, " : eq-elim "
>           , prettyBasic x, " ", prettyBasic q, "\n" ]
>             ++ pretty (i+1) pe ++ pretty (i+1) pf
>         IntroEq _ q -> concat
>           [ ind i, "* ", prettyBasic q, " : eq-intro\n" ]
>         Subst _ w s pf -> concat
>           [ ind i, "* ", prettyBasic w, " : sub "
>           , prettyBasic s, "\n" ]
>             ++ pretty (i+1) pf
>         IntroU _ w x y pf -> concat
>           [ ind i, "* ", prettyBasic w, " : forall-intro "
>           , prettyBasic x, " -> ", prettyBasic y, "\n" ]
>             ++ pretty (i+1) pf
>         ElimU _ w x e pf -> concat
>           [ ind i, "* ", prettyBasic w, " : forall-elim "
>           , prettyBasic x, " -> ", prettyBasic e, "\n" ]
>             ++ pretty (i+1) pf
>         IntroE _ w x e pf -> concat
>           [ ind i, "* ", prettyBasic w, " : exists-intro "
>           , prettyBasic x, " <- ", prettyBasic e, "\n" ]
>             ++ pretty (i+1) pf
>         ElimE _ w u x pe pi -> concat
>           [ ind i, "* ", prettyBasic w, " : exists-elim "
>           , prettyBasic x, " <- ", prettyBasic u, "\n" ]
>             ++ pretty (i+1) pe ++ pretty (i+1) pi
>         Use _ name q pfs -> concat
>           [ ind i, "* ", prettyBasic q, " : use "
>           , prettyBasic name, "\n" ]
>             ++ (concatMap (pretty (i+1)) pfs)
> 
>   parseBasic = p 0
>     where
>       p i = do
>         count (2*i) (char ' ')
>         char '*' >> spaceChars
>         q <- parseBasic
>         char ':' >> spaceChars
>         loc <- getLoc
>         just <- proofKeyword
>         spaceChars
>         case just of
>           "assumption" -> do
>             k <- read <$> many1 digit
>             newline
>             return (Assume loc k q)
> 
>           "hypothesis" -> do
>             n <- parseBasic
>             newline
>             return (Hyp loc n q)
> 
>           "discharge" -> do
>             n <- parseBasic
>             newline
>             pf <- p (i+1)
>             return (Dis loc n q pf)
> 
>           "eq-intro" -> do
>             newline
>             return (IntroEq loc q)
> 
>           "eq-elim" -> do
>             x <- parseBasic
>             spaceChars
>             w <- parseBasic
>             newline
>             pe <- p (i+1)
>             pf <- p (i+1)
>             return (ElimEq loc q x w pe pf)
> 
>           "sub" -> do
>             s <- parseBasic
>             newline
>             pf <- p (i+1)
>             return (Subst loc q s pf)
> 
>           "forall-intro" -> do
>             x <- parseBasic
>             string "->" >> spaceChars
>             y <- parseBasic
>             newline
>             pf <- p (i+1)
>             return (IntroU loc q x y pf)
> 
>           "forall-elim" -> do
>             x <- parseBasic
>             string "->" >> spaceChars
>             e <- parseBasic
>             newline
>             pf <- p (i+1)
>             return (ElimU loc q x e pf)
> 
>           "exists-intro" -> do
>             x <- parseBasic
>             string "<-" >> spaceChars
>             e <- parseBasic
>             newline
>             pf <- p (i+1)
>             return (IntroE loc q x e pf)
> 
>           "exists-elim" -> do
>             x <- parseBasic
>             string "<-" >> spaceChars
>             u <- parseBasic
>             newline
>             pe <- p (i+1)
>             pi <- p (i+1)
>             return (ElimE loc q u x pe pi)
> 
>           "use" -> do
>             n <- parseBasic
>             newline
>             pfs <- many $ try $ p (i+1)
>             return (Use loc n q pfs)
> 
>           x -> unexpected x

Parsing fancy proof lines:

> instance PrettyBasic FancyProofLine where
>   prettyBasic = \case
>     FancyHyp _ name q -> concat
>       [ prettyBasic q, " : hypothesis "
>       , prettyBasic name, "\n" ]
>     FancyDis _ name q u -> concat
>       [ prettyBasic q, " : discharge "
>       , prettyBasic name, "; ", show u, "\n" ]
>     FancyAssume _ i q -> concat
>       [ prettyBasic q, " : assumption "
>       , show i, "\n" ]
>     FancyIntroEq _ w -> concat
>       [ prettyBasic w, " : eq-intro\n" ]
>     FancyElimEq _ w x q u v -> concat
>       [ prettyBasic w, " : eq-elim "
>       , prettyBasic x, " ", prettyBasic q, "; "
>       , show u, ", ", show v, "\n" ]
>     FancySubst _ w s u -> concat
>       [ prettyBasic w, " : sub "
>       , prettyBasic s, "; "
>       , show u, "\n" ]
>     FancyIntroU _ w x y u -> concat
>       [ prettyBasic w, " : forall-intro "
>       , prettyBasic x, " -> ", prettyBasic y, "; "
>       , show u, "\n" ]
>     FancyElimU _ w x e u -> concat
>       [ prettyBasic w, " : forall-elim "
>       , prettyBasic x, " -> ", prettyBasic e, "; "
>       , show u, "\n" ]
>     FancyIntroE _ w x e u -> concat
>       [ prettyBasic w, " : exists-intro "
>       , prettyBasic x, " <- ", prettyBasic e, "; "
>       , show u, "\n" ]
>     FancyElimE _ w x q u v -> concat
>       [ prettyBasic w, " : exists-elim "
>       , prettyBasic x, " <- ", prettyBasic q, "; "
>       , show u, ", ", show v, "\n" ]
>     FancyUse _ name w us -> concat
>       [ prettyBasic w, " : use "
>       , prettyBasic name, "; "
>       , intercalate ", " $ map show us, "\n" ]
> 
>   parseBasic = parseLine <|> parseChain
>     where
>       parseLine :: Parser FancyProofLine
>       parseLine = do
>         w <- try parseBasic
>         spaceOrNewlines >> char ':' >> spaceChars
>         loc <- getLoc
>         just <- proofKeyword
>         spaceChars
>         case just of
>           "assumption" -> do
>             i <- read <$> many1 digit
>             newline
>             return $ FancyAssume loc i w
> 
>           "hypothesis" -> do
>             n <- parseBasic
>             newline
>             return $ FancyHyp loc n w
> 
>           "discharge" -> do
>             n <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             newline
>             return $ FancyDis loc n w u
> 
>           "eq-intro" -> do
>             newline
>             return $ FancyIntroEq loc w
> 
>           "eq-elim" -> do
>             x <- parseBasic
>             spaceChars
>             e <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             spaceChars >> char ',' >> spaceChars
>             v <- read <$> many1 digit
>             newline
>             return $ FancyElimEq loc w x e u v
> 
>           "sub" -> do
>             s <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             newline
>             return $ FancySubst loc w s u
> 
>           "forall-intro" -> do
>             x <- parseBasic
>             string "->" >> spaceChars
>             y <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             newline
>             return $ FancyIntroU loc w x y u
> 
>           "forall-elim" -> do
>             x <- parseBasic
>             string "->" >> spaceChars
>             e <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             newline
>             return $ FancyElimU loc w x e u
> 
>           "exists-intro" -> do
>             x <- parseBasic
>             string "<-" >> spaceChars
>             e <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             newline
>             return $ FancyIntroE loc w x e u
> 
>           "exists-elim" -> do
>             x <- parseBasic
>             string "<-" >> spaceChars
>             e <- parseBasic
>             char ';' >> spaceChars
>             u <- read <$> many1 digit
>             spaceChars >> char ',' >> spaceChars
>             v <- read <$> many1 digit
>             newline
>             return $ FancyElimE loc w x e u v
> 
>           "use" -> do
>             n <- parseBasic
>             char ';' >> spaceChars
>             us <- (map read) <$> (sepBy (many1 digit) (char ',' >> spaceChars))
>             newline
>             return $ FancyUse loc n w us
> 
>           x -> unexpected x
> 
>       parseChain :: Parser FancyProofLine
>       parseChain = do
>         e <- try parseBasic
>         spaceOrNewlines >> char ':' >> spaceChars
>         loc <- getLoc
>         string "chain" >> spaceChars
>         newline
>         ms <- many1 $ do
>           spaceChars >> string "==" >> spaceChars
>           e2 <- parseBasic
>           spaceOrNewlines >> char ':' >> spaceChars
>           flop <- option False (string "flop" >> spaceChars >> return True)
>           just <- parseChainJust
>           spaceChars
>           case just of
>             "hypothesis" -> do
>               n <- parseBasic
>               h <- parseAtIn
>               newline
>               return (e2, h, flop, ChainHyp loc n)
> 
>             "assumption" -> do
>               i <- read <$> many1 digit
>               spaceChars
>               h <- parseAtIn
>               newline
>               return (e2, h, flop, ChainAssume loc i)
> 
>             "use" -> do
>               n <- parseBasic
>               char ';' >> spaceChars
>               us <- (map read) <$> (sepBy (many1 digit) (char ',' >> spaceChars))
>               spaceChars
>               h <- parseAtIn
>               newline
>               return (e2, h, flop, ChainUse loc n us)
> 
>         return $ FancyChain loc e ms
> 
>       parseAtIn :: Parser (Maybe (Var Expr, Expr))
>       parseAtIn = option Nothing $ do
>         try (string "at" >> spaceChars)
>         w <- parseBasic
>         string "in" >> spaceChars
>         f <- parseBasic
>         return $ Just (w,f)
> 
>       parseChainJust :: Parser String
>       parseChainJust =
>         try (string "use") <|>
>         try (string "hypothesis") <|>
>         string "assumption"

Parsing fancy proofs:

> instance PrettyBasic FancyProof where
>   prettyBasic (FancyProof m) =
>     concatMap p $ M.assocs m
>     where
>       p (k,l) = concat
>         [ show k, ". ", prettyBasic l ]
> 
>   parseBasic = do
>     fancy <- many1 parseLine
>     return $ FancyProof $ M.fromList fancy
>     where
>       parseLine = do
>         k <- read <$> many1 digit
>         spaceChars >> char '.' >> spaceChars
>         l <- parseBasic
>         return (k,l)

And finally, parsing proofs in fancy style.

> instance PrettyFancy Proof where
>   prettyFancy p = prettyBasic (head $ serialize p)
> 
>   parseFancy = do
>     fancy <- parseBasic
>     case deserialize fancy of
>       Left err -> fail $ show err
>       Right p -> return p

Note that the fancy style proof parser includes an extra validation step that may fail.



Claims
------

Claims come in three flavors: type declarations, rules, and theorems. The syntax is roughly

```
type CONSTANT :: MONOTYPE

rule NAME
if
* JUDGEMENT
* JUDGEMENT
then
* JUDGEMENT

theorem NAME
* JUDGEMENT
  * JUDGEMENT
proof
1. JUDGEMENT;
2. JUDGEMENT; 1
```

> claimKeyword :: Parser String
> claimKeyword =
>   try (string "rule") <|>
>   try (string "definition") <|>
>   try (string "theorem") <|>
>   string "type"
> 
> instance PrettyBasic Claim where
>   prettyBasic = \case
>     Axiom t n ax -> concat
>       [ l, " ", prettyBasic n, "\n"
>       , prettyBasic ax, "\n"
>       ]
>       where
>         l = case t of
>           InferenceRule -> "rule"
>           Definition -> "definition"
>     Theorem n t pf -> concat
>       [ "theorem ", prettyBasic n, "\n"
>       , prettyBasic t, "\n"
>       , "proof\n", prettyBasic pf, "\n"
>       ]
>     TypeDecl c t -> concat
>       [ "type ", prettyBasic c, " :: ", prettyBasic t, "\n" ]
> 
>   parseBasic = do
>     m <- claimKeyword
>     spaceChars
>     case m of
>       "rule" -> do
>         n <- parseBasic
>         many1 newline
>         ax <- parseBasic <|> parseFancy
>         many newline
>         return (Axiom InferenceRule n ax)
> 
>       "definition" -> do
>         n <- parseBasic
>         many1 newline
>         ax <- parseBasic <|> parseFancy
>         many newline
>         return (Axiom Definition n ax)
> 
>       "theorem" -> do
>         n <- parseBasic
>         many1 newline
>         r <- parseBasic <|> parseFancy
>         many newline
>         string "proof" >> spaceChars
>         many1 newline
>         p <- parseBasic <|> parseFancy
>         many newline
>         return (Theorem n r p)
> 
>       "type" -> do
>         c <- parseBasic
>         string "::" >> spaceChars
>         t <- parseBasic
>         many newline
>         return (TypeDecl c t)
> 
>       m -> unexpected m



Modules
-------

A module is just a list of claims.

> instance PrettyBasic ModuleName where
>   prettyBasic (ModuleName n) = n
> 
>   parseBasic = do
>     n <- many1 $ oneOf _modulename_chars
>     spaceChars
>     return (ModuleName n)
> 
> instance PrettyBasic Module where
>   prettyBasic (Module n m) = concat
>     [ concatMap prettyBasic m ]
> 
>   parseBasic = do
>     name <- sourceName <$> getPosition
>     m <- many parseBasic
>     eof
>     return (Module (ModuleName name) m)



Errors
------

> prettyError :: VerifyError -> String
> prettyError = \case
>   HypAlreadyDefined n q -> unlines
>     [ "Hypothesis '" ++ (prettyBasic n) ++ "' already defined."
>     , prettyBasic q ]
>   HypNotFound n -> unlines
>     [ "Hypothesis '" ++ (prettyBasic n) ++ "' not found." ]
>   HypNotDischarged ns -> unlines $
>     [ "The following hypotheses were not discharged:" ]
>       ++ map (\n -> "  * " ++ prettyBasic n) ns

>   RuleDoesNotMatch loc n r qs -> unlines $
>     [ "At " ++ show loc
>     , "Rule '" ++ (prettyBasic n) ++ "' does not match."
>     , prettyBasic r ]
>       ++ map prettyBasic qs

>   ProofDoesNotMatch r q qs -> unlines $
>     [ "Proof does not match."
>     , prettyBasic r
>     , prettyBasic q ]
>       ++ map (\q -> "  * " ++ prettyBasic q) qs

>   AllVarMismatch loc x y j pf -> unlines
>     [ "ForAll elimination: bound variable mismatch."
>     , prettyBasic x ++ " does not match " ++ prettyBasic y
>     , prettyBasic j
>     , prettyBasic pf
>     ]

>   err -> show err
