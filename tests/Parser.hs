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

import Language.Lustre.Parser

main :: IO ()
main =
  do args <- getArgs
     let dir = "tests/parser-tests"
     fs0 <- getDirectoryContents dir
     let candidates = [ dir </> f | f <- fs0 ]
     let candidates = [ dir </> "dadic.lv6" ]
     fs  <- filterM doesFileExist candidates
     oks <- mapM parseFromFile fs
     unless (and oks) exitFailure

parseFromFile :: FilePath -> IO Bool
parseFromFile file =
  do txt <- Text.decodeLatin1 <$> BS.readFile file
     case parse program (Text.pack file) txt of
       Right a -> return True
       Left (ParseError mbR) ->
         do let loc = case mbR  of
                        Nothing -> "end of input"
                        Just r  -> prettySourcePos r
            putStrLn ("[FAIL] " ++ takeFileName file ++
                                      ": parse error at " ++ loc)
            return False
  `catch` \(SomeException e) ->
            do putStrLn ("[FAIL] " ++ displayException e)
               return False

