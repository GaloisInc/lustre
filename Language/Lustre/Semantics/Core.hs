module Language.Lustre.Semantics.Core where

import Data.Map ( Map )
import qualified Data.Map as Map

import Language.Lustre.Panic
import Language.Lustre.Core

data Value    = VInt    !Integer
              | VBool   !Bool
              | VReal   !Rational
              | VNil
                deriving Show

isNil :: Value -> Bool
isNil v =
  case v of
    VNil -> True
    _    -> False

isBool :: Value -> Maybe Bool
isBool v =
  case v of
    VBool b -> Just b
    _       -> Nothing

type Env      = Map Ident Value

evalLit :: Literal -> Value
evalLit lit =
  case lit of
    Int i  -> VInt i
    Real r -> VReal r
    Bool b -> VBool b

evalVar :: Env -> Ident -> Value
evalVar env x =
  case Map.lookup x env of
    Just v  -> v
    Nothing -> panic "evalAtom" [ "Undefined variable:"
                                , "*** Name: " ++ show x ]


evalAtom :: Env   {-^ Environment to for values of variables -} ->
            Atom  {-^ Evaluate this -} ->
            Value {-^ Value of the atom -}
evalAtom env atom =
  case atom of
    Lit l -> evalLit l
    Var x -> evalVar env x

evalExpr :: Maybe Env {-^ Current state, if transitioning -} ->
            Env       {- ^ Next state (partial) -} ->
            Expr      {- ^ Expression to evaluate -} ->
            Value
evalExpr cur next expr =
  case expr of
    Atom atom  -> evalAtom next atom

    a :-> b    -> case cur of
                    Nothing -> evalAtom next a
                    Just _  -> evalAtom next b

    Pre atom    -> case atom of
                     Lit l -> evalLit l
                     Var x -> case cur of
                                Nothing -> VNil
                                Just env -> evalVar env x

    a `When` b -> case evalAtom next b of
                    VBool True -> evalAtom next a
                    _          -> VNil

    Current a  -> case evalAtom next a of
                    VNil -> case cur of
                              Nothing  -> VNil
                              Just env -> evalAtom env a
                    v    -> v

    Prim op as ->
      case op of
        Not ->
          case vs of
            [ VNil ]    -> VNil
            [ VBool b ] -> VBool (not b)
            _           -> bad "1 bool"

        Neg ->
          case vs of
            [ VNil ]     -> VNil
            [ VInt n ]   -> VInt (negate n)
            [ VReal n ]  -> VReal (negate n)
            _            -> bad "1 number"

        IntCast ->
          case vs of
            [ VNil ]     -> VNil
            [ VReal r ]  -> VInt (truncate r)
            _            -> bad "1 real"

        RealCast ->
          case vs of
            [ VNil ]   -> VNil
            [ VInt n ] -> VReal (fromInteger n)
            _          -> bad "1 int"

        And ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VBool x, VBool y ]  -> VBool (x && y)
            _                     -> bad "2 bools"

        Or ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VBool x, VBool y ]  -> VBool (x || y)
            _                     -> bad "2 bools"

        Xor ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VBool x, VBool y ]  -> VBool (x /= y)
            _                     -> bad "2 bools"

        Implies ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VBool x, VBool y ]  -> VBool (not x || y)
            _                     -> bad "2 bools"

        Eq ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VBool x, VBool y ]  -> VBool (x == y)
            [ VInt x, VInt y ]    -> VBool (x == y)
            [ VReal x, VReal y ]  -> VBool (x == y)
            _                     -> bad "2 of the same type"

        Neq ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VBool x, VBool y ]  -> VBool (x /= y)
            [ VInt x, VInt y ]    -> VBool (x /= y)
            [ VReal x, VReal y ]  -> VBool (x /= y)
            _                     -> bad "2 of the same type"

        Lt ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VBool (x < y)
            [ VReal x, VReal y ]  -> VBool (x < y)
            _                     -> bad "2 numbers"

        Leq ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VBool (x <= y)
            [ VReal x, VReal y ]  -> VBool (x <= y)
            _                     -> bad "2 numbers"

        Gt ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VBool (x > y)
            [ VReal x, VReal y ]  -> VBool (x > y)
            _                     -> bad "2 numbers"

        Geq ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VBool (x >= y)
            [ VReal x, VReal y ]   -> VBool (x >= y)
            _                     -> bad "2 numbers"

        Add ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VInt  (x + y)
            [ VReal x, VReal y ]   -> VReal (x + y)
            _                     -> bad "2 numbers"

        Sub ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VInt  (x - y)
            [ VReal x, VReal y ]   -> VReal (x - y)
            _                     -> bad "2 numbers"

        Mul ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VInt  (x * y)
            [ VReal x, VReal y ]   -> VReal (x * y)
            _                     -> bad "2 numbers"

        Div ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VInt (quot x y)
            [ VReal x, VReal y ]   -> VReal (x / y)
            _                     -> bad "2 numbers"

        Mod ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VInt (rem x y)
            _                     -> bad "2 ints"

        Power ->
          case vs of
            [ VNil, _ ]           -> VNil
            [ _, VNil ]           -> VNil
            [ VInt x, VInt y ]    -> VInt  (x ^ y)
            [ VReal x, VInt y ]   -> VReal (x ^ y)
            _                     -> bad "1 number and 1 int"

        ITE ->
          case vs of
            [ VNil, _, _ ]        -> VNil
            [ VBool b, x, y ]     -> if b then x else y
            _                     -> bad "1 bool, and 2 of the same type"

        AtMostOne
          | any isNil vs              -> VNil
          | Just bs <- mapM isBool vs -> VBool $ case filter id bs of
                                                   _ : _ : _ -> False
                                                   _         -> True
          | otherwise                 -> bad "all bool"

        Nor
          | any isNil vs              -> VNil
          | Just bs <- mapM isBool vs -> VBool (not (or bs))
          | otherwise                 -> bad "all booleans"

      where
      vs = map (evalAtom next) as

      bad y = panic "evalExpr" [ "Type error:"
                               , "*** Operator: " ++ show op
                               , "*** Expected: " ++ y
                               , "*** Got: "      ++ show vs ]







