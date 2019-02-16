{-# Language OverloadedStrings #-}
module Main(main) where

import Text.Read(readMaybe)
import Text.PrettyPrint((<+>))
import Control.Exception(catches,Handler(..),throwIO,catch)
import Control.Monad(when)
import Data.IORef(newIORef,readIORef,atomicModifyIORef')
import System.IO(stdin,stdout,stderr,hFlush,hPutStrLn,hPrint
                , openFile, IOMode(..), hGetContents )
import System.IO.Error(isEOFError)
import System.Environment
import qualified Data.Map as Map
import Numeric(readSigned,readFloat)

import Language.Lustre.AST(Program(..))
import Language.Lustre.Core
import Language.Lustre.Semantics.Core
import Language.Lustre.Parser(parseProgramFromFileLatin1, ParseError)
import Language.Lustre.Driver
import Language.Lustre.Monad
import Language.Lustre.Pretty(pp)


conf :: LustreConf
conf = LustreConf
  { lustreInitialNameSeed = Nothing
  , lustreLogHandle       = stdout
  , lustreNoTC            = True
  }

main :: IO ()
main =
  do args <- getArgs
     case args of
       [f]   -> runFromFile f Nothing
       [f,i] -> runFromFile f (Just i)
       _     -> hPutStrLn stderr "USAGE: lustre FILE [INPUT_FILE]"

runFromFile :: FilePath -> Maybe FilePath -> IO ()
runFromFile file mbIn =
  do a <- parseProgramFromFileLatin1 file
     case a of
       ProgramDecls ds ->
         do (ws,nd) <- runLustre conf $
                         do (_,nd) <- quickNodeToCore Nothing ds
                            warns  <- getWarnings
                            pure (warns,nd)
            mapM_ showWarn ws
            sIn <- newIn mbIn
            runNodeIO sIn nd
       _ -> hPutStrLn stderr "We don't support packages for the moment."
   `catches`
     [ Handler $ \e -> showErr (e :: ParseError)
     , Handler $ \e -> showErr (e :: LustreError)
     ]
  where
  showErr e = hPrint stderr (pp e)
  showWarn w = hPrint stderr (pp w)


data In = In
  { hasMore   :: IO Bool
  , nextToken :: IO String
  , echo      :: Bool
  }

newIn :: Maybe FilePath -> IO In
newIn mb =
  do (h,e) <- case mb of
                Nothing -> pure (stdin,False)
                Just f  -> do h <- openFile f ReadMode
                              pure (h,True)
     ws0 <- words <$> hGetContents h
     r  <- newIORef ws0
     pure In { hasMore = not . null <$> readIORef r
             , nextToken = atomicModifyIORef' r $ \ws -> case ws of
                                                           [] -> ([],"")
                                                           w : more -> (more,w)
             , echo = e
             }

runNodeIO :: In -> Node -> IO ()
runNodeIO sIn node =
  do print (ppNode node)
     go (1::Integer) s0
   `catch` \e -> if isEOFError e then pure () else throwIO e
  where
  (s0,step)   = initNode node Nothing

  go n s = do more <- hasMore sIn
              when more $
                do putStrLn ("--- Step " ++ show n ++ " ---")
                   s1  <- step s <$> getInputs
                   mapM_ (showOut s1) (nOutputs node)
                   go (n+1) s1

  showOut s x = print (ppIdent x <+> "=" <+> ppValue (evalVar s x))

  getInputs   = Map.fromList <$> mapM getInput (nInputs node)

  getInput b@(_ ::: t `On` _) =
    do putStr (show (ppBinder b <+> " = "))
       hFlush stdout
       doGet b

  doGet :: Binder -> IO (Ident,Value)
  doGet b@(x ::: t) =
    do txt <- nextToken sIn
       when (echo sIn) (putStrLn txt)
       case parseVal (typeOfCType t) txt of
         Just ok -> pure (x, ok)
         Nothing -> do putStrLn ("Invalid " ++ show (ppCType t))
                       getInput b

parseVal :: Type -> String -> Maybe Value
parseVal t s =
  case t of
    TBool -> VBool <$> readMaybe s
    TInt  -> VInt  <$> readMaybe s
    TReal -> case readSigned readFloat s of
               [(n,"")] -> Just (VReal n)
               _        -> Nothing



