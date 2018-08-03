{-# Language OverloadedStrings #-}
module Main(main) where

import System.Exit
import qualified Data.Text as Text

import Data.String

import Language.Lustre.Core

main :: IO ()
main =
  case ex1 of
    Left err -> do putStrLn "Cycles:"
                   mapM_ (print . map ppBinder) err
                   exitFailure
    Right ok -> print (ppNode ok)


instance IsString Ident where
  fromString = Ident . Text.pack

instance IsString Name where
  fromString = Name . Text.pack

instance IsString Atom where
  fromString = Var . fromString

instance IsString Expr where
  fromString = Atom . fromString

instance Num Literal where
  fromInteger = Int

instance Fractional Literal where
  fromRational = Real

instance Num Atom where
  fromInteger = Lit . fromInteger

instance Fractional Atom where
  fromRational = Lit . fromRational

instance Num Expr where
  fromInteger = Atom . fromInteger

instance Fractional Expr where
  fromRational = Atom . fromRational


ex1 = toNode <$> orderedEqns
        [ "nats" ::: TInt := "start" :-> "next"
        , "next" ::: TInt := Call "add" [ 1, "prev" ]
        , "prev" ::: TInt := Pre "nats"
        ]
  where
  toNode eqns =
    Node { nName    = "natsFrom"
         , nInputs  = [ "start" ::: TInt ]
         , nOutputs = [ "nats" ]
         , nAsserts = []
         , nEqns    = eqns
         }


