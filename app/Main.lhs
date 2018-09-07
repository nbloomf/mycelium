---
title: Main
---

This module bundles the proof parser and checker in a command line tool. I can think of several interesting things such a tool could do -- like open an interactive shell for type checking or assist in writing proofs -- but for now we'll just do one thing: parse and validate a list of proofs.

I'm a big fan of literate programming. To facilitate this with mycelium, we'll have the tool automatically ignore any lines not between

    ~~~ {.mycelium

and

    ~

This way we can write mycelium proofs in markdown, and markdown processors (like pandoc) can display the proofs as code.

> module Main where
> 
> import Data.List
> import Data.Map
>   ( size )
> import System.Environment
> import System.Exit
> import Text.ParserCombinators.Parsec
> 
> import Mycelium

The main program takes a list of filenames, parses them as modules, and checks the claims in each one in order.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   ms <- mapM readModule args
> 
>   case checkModules ms (emptyTypeEnv, RuleEnv mempty) of
>     Left err -> do
>       putStrLn $ prettyError err
>       exitFailure
>     Right (TypeEnv types, RuleEnv rules) -> do
>       putStrLn $ "rules: " ++ (show $ size rules)
>       putStrLn $ "types: " ++ (show $ size types)
>       return ()
> 
> readModule :: FilePath -> IO Module
> readModule path = do
>   contents <- processLiterate <$> readFile path
>   case contents of
>     Nothing -> do
>       putStrLn "Malformed module."
>       exitFailure
>     Just m -> do
>       case runParser parseBasic () path m of
>         Left err -> do
>           putStrLn $ show err
>           exitFailure
>         Right m -> return m

`processLiterate` pulls out only the lines we want.

> processLiterate :: String -> Maybe String
> processLiterate x = 
>   unlines <$>
>     spliceBy
>       (isPrefixOf "~~~ {.mycelium")
>       (isPrefixOf "~")
>       (lines x)
> 
> spliceBy :: (a -> Bool) -> (a -> Bool) -> [a] -> Maybe [a]
> spliceBy a b xs =
>   case dropWhile (not . a) xs of
>     [] -> Just []
>     _:ys -> case span (not . b) ys of
>       (w,[]) -> Nothing
>       (w,_:zs) -> (w ++) <$> spliceBy a b zs
