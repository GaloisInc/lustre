{-# Language OverloadedStrings #-}
module Language.Lustre.Semantics.Value
  ( module Language.Lustre.Semantics.Value
  , Stream(..)
  ) where

import Text.PrettyPrint as P
import Language.Lustre.AST
import Language.Lustre.Semantics.Stream
import Language.Lustre.Pretty

-- | The universe of basic values.
-- These are the values used for a specific time instance.
data Value    = VInt    !Integer
              | VBool   !Bool
              | VReal   !Rational
              | VNil
              | VEnum   !Name !Ident              -- ^ Type, value
              | VStruct !Name ![(Ident,Value)]    -- ^ Type, fields
              | VArray  ![Value]
                deriving Show


instance Eq Value where
  x == y =
    case (x,y) of
      (VInt a,  VInt b)        -> a == b
      (VBool a, VBool b)       -> a == b
      (VReal a, VReal b)       -> a == b
      (VEnum t1 a, VEnum t2 b) -> t1 == t2 && a == b
      (VArray as, VArray bs)   -> cmpArr as bs
      (VStruct t1 as, VStruct t2 bs) | t1 == t2 -> cmpStr as bs
      _ -> False -- Type error

    where
    cmpArr as bs =
      case (as,bs) of
        ([],[])          -> True
        (a : xs, b : ys) -> a == b && cmpArr xs ys
        _                -> False

    cmpStr as bs =
      case (as,bs) of
        ([],[]) -> True
        ((f,v):more, fs) ->
          case getField f fs of
            Nothing -> False
            Just (v2,fs') -> v == v2 && cmpStr more fs'
        _ -> False -- Malformed structs

    getField nm fs =
      case fs of
        [] -> Nothing
        (f,a) : more -> if nm == f then Just (a,more)
                                   else do (a',more') <- getField nm more
                                           return (a', (f,a) : more')



-- | A reactive value represents the evolution of a basic value over time,
-- as driven by a clock.
type ReactValue = Stream EvalM Step


-- | The evaluation monad.
type EvalM      = Either Error
type Error      = String

-- | A "step" is either an exisitng element,
-- or an element that has been skipped by a clock.
data Step     = Emit !Value   -- ^ An existing element.
              | Skip !Integer -- ^ Skipped by clock at the given depth
                              -- (0 is the current clock)
                deriving Show

-- | Crash evaluation. We'd like to avoid calls to this.
crash :: String -> String -> EvalM a
crash x y = Left (x ++ ": " ++ y)

typeError :: String -> String -> EvalM a
typeError x y = crash x ("Type error, expected " ++ y)


--------------------------------------------------------------------------------

instance Pretty Value where
  ppPrec _ val =
    case val of
      VInt n -> integer n
      VBool b -> text (show b)
      VReal r -> double (fromRational r) -- XXX
      VNil -> "nil"
      VEnum _ a -> pp a
      VStruct _ fs -> braces (hsep (punctuate comma (map ppF fs)))
        where ppF (x,y) = pp x <+> "=" <+> pp y
      VArray vs -> brackets (hsep (punctuate comma (map pp vs)))

