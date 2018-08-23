{-# Language OverloadedStrings #-}
module Main(main) where

import System.Exit(exitFailure)
import System.Directory(getDirectoryContents, doesFileExist)
import System.FilePath(takeFileName, (</>))
import System.IO(hFlush,stdout)
import System.Environment(getArgs)
import Control.Monad(unless, filterM)
import Control.Exception(catch, SomeException(..), displayException)
import Text.PrettyPrint
import Data.Graph(SCC(..))
import Data.List(sort)

import Language.Lustre.Parser
import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Transform.NoStatic

main :: IO ()
main =
  do args <- getArgs
     let dir = "tests/no-static"
     fs0 <- getDirectoryContents dir
     let candidates = [ dir </> f | f <- sort fs0 ]
     fs  <- filterM doesFileExist candidates
     oks <- mapM checkFile fs
     unless (and oks) exitFailure

checkFile :: FilePath -> IO Bool
checkFile file =
  do a <- parseProgramFromFileLatin1 file
     case a of
       ProgramDecls ds ->
         do print $ vcatSep $ map pp $ quickEvalDecls True ds
            putStrLn "----------------------------"
            return True
       _ -> do putStrLn "Packages are not yet supported"
               return False
  `catch` \(SomeException e) ->
            do putStrLn ("[FAIL] " ++ displayException e)
               return False



