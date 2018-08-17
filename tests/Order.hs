{-# Language OverloadedStrings #-}
module Main(main) where

import System.Exit(exitFailure)
import System.Directory(getDirectoryContents, doesFileExist)
import System.FilePath(takeFileName, (</>))
import System.IO(hFlush,stdout)
import System.Environment(getArgs)
import Control.Monad(unless, filterM)
import Control.Exception(catch, SomeException(..), displayException)
import qualified Data.ByteString as BS
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Encoding.Error as Text
import Text.Show.Pretty(pPrint)

import Language.Lustre.Parser
import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Transform.OrderDecls

main :: IO ()
main =
  do args <- getArgs
     let dir = "tests/parser-tests"
     fs0 <- getDirectoryContents dir
     let candidates = [ dir </> f | f <- fs0 ]
     -- let candidates = [ dir </> "yav.lv6" ]
     fs  <- filterM doesFileExist candidates
     let fs = ["test.lus"]
     oks <- mapM checkFile fs
     unless (and oks) exitFailure

checkFile :: FilePath -> IO Bool
checkFile file =
  do a <- parseProgramFromFileLatin1 file
     case a of
       ProgramDecls ds ->
         do pPrint (orderTopDecls ds)
            return True
       _ -> do putStrLn "Packages arenot yet supported"
               return False
  `catch` \(SomeException e) ->
            do putStrLn ("[FAIL] " ++ displayException e)
               return False

