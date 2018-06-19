{-# Language OverloadedStrings, HexFloatLiterals #-}
module Main(main) where

import Data.Text(Text)
import Data.Maybe(mapMaybe)
import System.Exit(exitFailure, exitSuccess)
import Language.Lustre.Parser.Lexer

type Test = (Text, Text, [Token])

tests :: [Test]
tests =
  [ test "Identifiers"
          "Hello A::B"
          [ TokIdent, TokQualIdent "A" "B" ]

  , test "Integers"
          "102 0x23 0xAAff +102 -0x23"
          $ [ TokInt 102, TokInt 35, TokInt 43775
            , TokPlus, TokInt 102, TokMinus, TokInt 35 ]

  , test "Reals 10"
          "1.1 1. .1 2e10 2e+10 2e-10 1.e3 1.2"
          $ map TokReal [ 1.1, 1, 0.1, 2e10, 2e10, 2e-10 , 1e3, 1.2 ]

  , test "Reals 16"
          "0x10.1 0x1. 0x0.11 0x.11p-1"
          $ map TokReal [ 0x10.1, 1, 0x0.11, 0x0.11p-1 ]

  , test "Comments"
          "(* 1*'\n *) 2 (* 3 *) 4 /* 5 */ 6 /* 7 */ /*****\n****\n*****/"
          (map TokInt [ 2,4,6])

  , test "Comments2"
          "/* 1 *******/ 2 /* 3 ******/ 4 /* */"
          (map TokInt [ 2,4 ])

  , test "Comments3"
          "(* 1 *******) 2 (* 3 ******) 4 (* *)"
          (map TokInt [ 2,4 ])



  ]
  where
  test a b c = (a,b,c ++ [TokEOF])

main :: IO ()
main = do mapM_ reportProblem problems
          if null problems then exitSuccess else exitFailure
  where
  problems = mapMaybe findProblem tests
  reportProblem (nm, ls, e) =
    do putStrLn ("Test " ++ show nm ++ " failed.")
       putStrLn ("*** Expected: " ++ show e)
       putStrLn ("*** Lexed:    " ++ show ls)


findProblem :: Test -> Maybe (Text, [Token], [Token])
findProblem (nm,txt,expected)
  | lexed == expected = Nothing
  | otherwise         = Just (nm, lexed, expected)
  where
  lexed = map lexemeToken (lexer (initialInput nm txt))

