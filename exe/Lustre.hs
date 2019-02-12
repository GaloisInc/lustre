{-# Language OverloadedStrings #-}
module Main(main) where

import Text.Read(readMaybe)
import Text.PrettyPrint((<+>))
import Control.Exception(catches,Handler(..),throwIO,catch)
import System.IO(stdin,stdout,stderr,hFlush,hPutStrLn,hPrint,hIsTerminalDevice)
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

  go n s      = do s1 <- step s <$> getInputs
                   putStrLn ("--- Step " ++ show n ++ " ---")
                   mapM_ (showOut s1) (nOutputs node)
                   go (n+1) s1

  showOut s x = print (ppIdent x <+> "=" <+> ppValue (evalVar s x))

  getInput b@(_ ::: t `On` _) =
    do term <- hIsTerminalDevice stdin
       let msg = show (ppBinder b <+> " = ")
       echo <- if term then putStr msg >> hFlush stdout >> pure Nothing
                       else pure (Just msg)
       case t of
         TInt  -> doGet echo b VInt
         TReal -> doGet echo b VReal
         TBool -> doGet echo b VBool

  doGet :: Read a => Maybe String -> Binder -> (a -> Value) -> IO (Ident,Value)
  doGet msg b@(x ::: t) con =
    do txt <- getLine
       case readMaybe txt of
         Just ok -> do case msg of
                          Nothing -> pure ()
                          Just m  -> putStr (m ++ txt ++ "\n") >> hFlush stdout
                       pure (x, con ok)
         Nothing -> do putStrLn ("Invalid " ++ show (ppCType t))
                       getInput b



