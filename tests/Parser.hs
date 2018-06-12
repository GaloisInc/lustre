{-# Language OverloadedStrings #-}
module Main(main) where

import System.Exit

import Language.Lustre.Parser

main :: IO ()
main =
  case parse expression "F" "A::B::C" of
    Right a -> print a
    Left err -> do print err
                   exitFailure

