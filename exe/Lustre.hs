{-# Language OverloadedStrings #-}
module Main(main) where

import Text.Read(readMaybe)
import Text.PrettyPrint((<+>))
import System.IO(stdout,stderr,hFlush,hPutStrLn)
import System.Environment
import qualified Data.Map as Map

import Language.Lustre.AST(Program(..))
import Language.Lustre.TypeCheck
import Language.Lustre.Core
import Language.Lustre.Semantics.Core
import Language.Lustre.Parser(parseProgramFromFileLatin1)
import Language.Lustre.Transform.Desugar

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
         case quickCheckDecls ds of
           Left err -> hPutStrLn stderr (show err)
           Right _  -> runNodeIO (desugarNode ds Nothing)
       _ -> hPutStrLn stderr "We don't support packages for the moment."


runNodeIO :: Node -> IO ()
runNodeIO node = do print (ppNode node)
                    go (1::Integer) s0
  where
  (s0,step) = initNode node Nothing

  getInputs   = Map.fromList <$> mapM getInput (nInputs node)

  go n s      = do s1 <- step s <$> getInputs
                   putStrLn ("--- Step " ++ show n ++ " ---")
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
       case readMaybe txt of
         Just ok -> pure (x, con ok)
         Nothing -> do putStrLn ("Invalid " ++ show (ppCType t))
                       getInput b



