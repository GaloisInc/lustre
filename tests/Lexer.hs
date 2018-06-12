{-# Language OverloadedStrings #-}
module Main(main) where

import Data.Text(Text)
import Language.Lustre.Lexer

main :: IO ()
main =
  do runTest "Identifiers" "Hello World A::B"
     runTest "Integer" "102 0x23 0xAAff +102 +0x23 -102 -0x23"
     runTest "Reals 10"  "1.1 1. .1 2e10 2e+10 2e-10 1.e3 0x1"
     runTest "Reals 16"  "0x10.1 -0x.11p-1"
     runTest "EOF 1" ""
     runTest "EOF 2" "A\n"

runTest :: String -> Text -> IO ()
runTest nm txt =
  do putStrLn ("=== " ++ nm ++ " ===")
     mapM_ (putStrLn . pp) $ lexer $ initialInput "(stdin)" txt
     putStrLn (replicate 80 '=')
     putStrLn ""

  where pp x = unwords [ show (lexemeText x)
                       , show (lexemeToken x)
                       , prettySourceRange (lexemeRange x)
                       ]

