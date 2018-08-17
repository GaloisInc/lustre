{-# Language OverloadedStrings #-}
module Main(main) where

import System.Exit(exitFailure)
import System.Directory(getDirectoryContents, doesFileExist)
import System.FilePath(takeFileName, (</>))
import System.IO(hFlush,stdout)
import System.Environment(getArgs)
import Control.Monad(unless, filterM)
import Control.Exception(catch, SomeException(..), displayException)

import Language.Lustre.Parser

main :: IO ()
main =
  do args <- getArgs
     let dir = "tests/parser-tests"
     fs0 <- getDirectoryContents dir
     let candidates = [ dir </> f | f <- fs0 ]
     -- let candidates = [ dir </> "yav.lv6" ]
     fs  <- filterM doesFileExist candidates
     oks <- mapM checkFile fs
     unless (and oks) exitFailure

checkFile :: FilePath -> IO Bool
checkFile file =
  do _ <- parseProgramFromFileLatin1 file
     pure True
  `catch` \(SomeException e) ->
            do putStrLn ("[FAIL] " ++ displayException e)
               return False
