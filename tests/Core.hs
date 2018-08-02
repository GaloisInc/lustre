module Main(main) where

import System.Exit
import qualified Data.Text as Text

import Language.Lustre.Core


main :: IO ()
main =
  case orderedEqns ex1 of
    Left err -> do putStrLn "Cycles:"
                   mapM_ (print . map ppIdent) err
                   exitFailure
    Right ok -> mapM_ (print . ppEqn) ok



ex1 = [ Eqn (v "nats") (EFby (i 0) (ev "a"))
      , Eqn (v "a")    (add (ev "b") (i 1))
      , Eqn (v "b")    (EPre (ev "nats"))
      ]
  where
  ev      = AVar . v 
  v x     = Ident (Text.pack x)
  i x     = ALit (Int x)
  add a b = ECall (Name "add") [ a,b ]


