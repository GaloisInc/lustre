{-# Language OverloadedStrings #-}
module Main(main) where

import Text.Read(readMaybe)
import Text.PrettyPrint((<+>))
import Control.Exception(catches,Handler(..),throwIO,catch)
import Control.Monad(when,unless)
import Data.IORef(newIORef,readIORef,writeIORef)
import System.IO(stdin,stdout,stderr,hFlush,hPutStrLn,hPrint
                , openFile, IOMode(..), hGetContents )
import System.IO.Error(isEOFError,mkIOError,eofErrorType)
import System.Exit(exitSuccess)
import qualified Data.Map as Map
import Numeric(readSigned,readFloat)
import SimpleGetOpt
import qualified Data.Set as Set

import Language.Lustre.AST(Program(..))
import Language.Lustre.Core
import Language.Lustre.Semantics.Core
import Language.Lustre.Parser(parseProgramFromFileLatin1, ParseError)
import Language.Lustre.Driver
import Language.Lustre.Monad
import Language.Lustre.Pretty(pp)

import Options


computeConf :: Options -> IO LustreConf
computeConf opts =
  do logH <- case logFile opts of
               Nothing -> pure stdout
               Just f  -> openFile f WriteMode
     pure LustreConf { lustreInitialNameSeed = Nothing
                     , lustreLogHandle = logH
                     , lustreNoTC = False
                     , lustreDumpAfter = dumpAfter opts
                     }


main :: IO ()
main =
  do opts <- getOptsX options
     when (showHelp opts) $
       do putStrLn (usageString options)
          exitSuccess

     a <- case progFile opts of
            Nothing ->
              throwIO (GetOptException ["No Lustre file was speicifed."])
            Just f -> parseProgramFromFileLatin1 f

     case a of
       ProgramDecls ds ->
         do conf <- computeConf opts
            (ws,nd) <- runLustre conf $
                         do unless (Set.null (lustreDumpAfter conf))
                                   (setVerbose True)
                            (_,nd) <- quickNodeToCore Nothing ds
                            warns  <- getWarnings
                            pure (warns,nd)
            mapM_ showWarn ws
            sIn <- newIn (inputFile opts)
            runNodeIO sIn nd
       _ -> hPutStrLn stderr "We don't support packages for the moment."
   `catches`
     [ Handler $ \e -> showErr (e :: ParseError)
     , Handler $ \e -> showErr (e :: LustreError)
     , Handler $ \(GetOptException es) ->
                    do mapM_ (hPutStrLn stderr) es
                       hPutStrLn stderr ""
                       hPutStrLn stderr (usageString options)

     ]
  where
  showErr e  = hPrint stderr (pp e)
  showWarn w = hPrint stderr (pp w)


data In = In
  { nextToken :: IO String
  , echo      :: Bool
  }

newIn :: Maybe FilePath -> IO In
newIn mb =
  do (h,e) <- case mb of
                Nothing -> pure (stdin,False)
                Just f  -> do h <- openFile f ReadMode
                              pure (h,True)
     ws0 <- words <$> hGetContents h
     r   <- newIORef ws0
     pure In { nextToken = -- assumes single threaded
                do ws <- readIORef r
                   case ws of
                     [] -> ioError $ mkIOError eofErrorType
                                      "(EOF)" Nothing Nothing
                     w : more -> do writeIORef r more
                                    pure w
             , echo = e
             }

runNodeIO :: In -> Node -> IO ()
runNodeIO sIn node =
  go (1::Integer) s0
   `catch` \e -> if isEOFError e then putStrLn "(EOF)" else throwIO e
  where
  (s0,step)   = initNode node Nothing

  go n s = do putStrLn ("--- Step " ++ show n ++ " ---")
              s1  <- step s <$> getInputs
              mapM_ (showOut s1) (nOutputs node)
              go (n+1) s1

  showOut s x = print (pp x <+> "=" <+> ppValue (evalVar s x))

  getInputs   = Map.fromList <$> mapM getInput (nInputs node)

  ppinfo = identVariants node

  getInput b@(x ::: ct) =
    do putStr (show (ppBinder ppinfo b <+> " = "))
       hFlush stdout
       txt <- nextToken sIn
       when (echo sIn) (putStrLn txt)
       case parseVal (typeOfCType ct) txt of
         Just ok -> pure (x,ok)
         Nothing -> do putStrLn ("Invalid " ++ show (ppCType ppinfo ct))
                       getInput b

parseVal :: Type -> String -> Maybe Value
parseVal t s
  | ["-"] == words s = Just VNil
  | otherwise =
  case t of
    TBool -> VBool <$> readMaybe s
    TInt  -> VInt  <$> readMaybe s
    TReal -> case readSigned readFloat s of
               [(n,"")] -> Just (VReal n)
               _        -> Nothing



