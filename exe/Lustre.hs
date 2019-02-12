{-# Language OverloadedStrings #-}
module Main(main) where

import Text.Read(readMaybe)
import Text.PrettyPrint((<+>))
import Control.Exception(catches,Handler(..),throwIO,catch)
import Control.Monad(unless)
import System.IO(stdin,stdout,stderr,hFlush,hPutStrLn,hPrint,hGetEcho)
import System.IO.Error(isEOFError)
import System.Environment
import qualified Data.Map as Map

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
  }

main :: IO ()
main =
  do args <- getArgs
     case args of
       [f] -> runFromFile f
       _   -> hPutStrLn stderr "USAGE: lustre FILE"

runFromFile :: FilePath -> IO ()
runFromFile file =
  do a <- parseProgramFromFileLatin1 file
     case a of
       ProgramDecls ds ->
         do (ws,nd) <- runLustre conf $
                         do (_,nd) <- quickNodeToCore Nothing ds
                            warns  <- getWarnings
                            pure (warns,nd)
            mapM_ showWarn ws
            runNodeIO nd
       _ -> hPutStrLn stderr "We don't support packages for the moment."
   `catches`
     [ Handler $ \e -> showErr (e :: ParseError)
     , Handler $ \e -> showErr (e :: LustreError)
     ]
  where
  showErr e = hPrint stderr (pp e)
  showWarn w = hPrint stderr (pp w)


runNodeIO :: Node -> IO ()
runNodeIO node = do print (ppNode node)
                    go (1::Integer) s0
                  `catch` \e -> if isEOFError e then pure () else throwIO e
  where
  (s0,step)   = initNode node Nothing

  getInputs   = Map.fromList <$> mapM getInput (nInputs node)

  go n s      = do putStrLn ("--- Step " ++ show n ++ " ---")
                   s1 <- step s <$> getInputs
                   mapM_ (showOut s1) (nOutputs node)
                   go (n+1) s1

  showOut s x = print (ppIdent x <+> "=" <+> ppValue (evalVar s x))

  getInput b@(_ ::: t `On` _) =
    do putStr (show (ppBinder b <+> " = "))
       hFlush stdout
       case t of
         TInt  -> doGet b VInt
         TReal -> doGet b VReal
         TBool -> doGet b VBool

  doGet :: Read a => Binder -> (a -> Value) -> IO (Ident,Value)
  doGet b@(x ::: t) con =
    do txt <- getLine
       echoOn <- hGetEcho stdin
       unless echoOn $ putStrLn txt
       case readMaybe txt of
         Just ok -> pure (x, con ok)
         Nothing -> do putStrLn ("Invalid " ++ show (ppCType t))
                       getInput b



