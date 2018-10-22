module Language.Lustre.Semantics.BuiltIn
  ( -- * Static

    -- * Constants
    sInt, sReal, sBool

    -- ** Coercions
  , sReal2Int, sInt2Real

    -- ** Logical operators
  , sNot, sAnd, sOr, sXor, sImplies, sBoolRed

    -- ** Relations and choices
  , sEq, sNeq, sLt, sGt, sLeq, sGeq, sITE

    -- ** Arithmetic
  , sNeg, sAdd, sSub, sMul, sDiv, sMod, sPow

    -- * Data structures
  , sArray, sReplicate, sConcat, sSelectIndex, sSelectSlice
  , sSelectField

  ) where

import Data.List(genericReplicate,genericDrop,genericIndex,genericLength)

import Language.Lustre.AST
import Language.Lustre.Semantics.Value



--------------------------------------------------------------------------------
-- Static

sInt :: Integer -> EvalM Value
sInt x = pure (VInt x)

sReal :: Rational -> EvalM Value
sReal x = pure (VReal x)

sBool :: Bool -> EvalM Value
sBool x = pure (VBool x)

sArray :: [Value] -> EvalM Value
sArray x = pure (VArray x)

sNot :: Value -> EvalM Value
sNot v =
  case v of
    VBool x -> sBool (not x)
    _       -> typeError "not" "a `bool`"

sNeg :: Value -> EvalM Value
sNeg v =
  case v of
    VInt x  -> sInt (negate x)
    VReal x -> sReal (negate x)
    _       -> typeError "uminus" "a `real` or a `number`"

sReal2Int :: Value -> EvalM Value
sReal2Int v =
  case v of
    VReal x -> sInt (truncate x)
    _       -> typeError "real2int" "a `real`"

sInt2Real :: Value -> EvalM Value
sInt2Real v =
  case v of
    VInt x -> sReal (fromInteger x)
    _      -> typeError "int2real" "an `int`"


sOp2 :: (Value -> Value -> EvalM Value) -> Value -> Value -> EvalM Value
sOp2 f u v =
  case (u,v) of
    _        -> f u v

sBoolOp2 :: String -> (Bool -> Bool -> Bool) -> Value -> Value -> EvalM Value
sBoolOp2 name f =
  sOp2 $ \u v ->
    case (u,v) of
      (VBool x, VBool y) -> sBool (f x y)
      _                  -> typeError name "`(bool,bool)`"

sAnd, sOr, sXor, sImplies :: Value -> Value -> EvalM Value
sAnd      = sBoolOp2 "and"      (&&)
sOr       = sBoolOp2 "or"       (||)
sXor      = sBoolOp2 "xor"      (/=)
sImplies  = sBoolOp2 "implies"  (\p q -> not p || q)

sEq :: Value -> Value -> EvalM Value
sEq = sOp2 $ \u v -> sBool (u == v)

sNeq :: Value -> Value -> EvalM Value
sNeq = sOp2 $ \u v -> sBool (u /= v)

sCmpOp :: String -> (Ordering -> Bool) -> Value -> Value -> EvalM Value
sCmpOp name f = sOp2 $ \u v ->
  case (u,v) of
    (VInt x,  VInt y)  -> sBool (f (compare x y))
    (VReal x, VReal y) -> sBool (f (compare x y))
    _ -> typeError name "`(int,int)` or `(real,real)`"

sLt, sGt, sLeq, sGeq :: Value -> Value -> EvalM Value
sLt  = sCmpOp "lt" (== LT)
sGt  = sCmpOp "gt" (== GT)
sLeq = sCmpOp "leq" (\x -> x == LT || x == EQ)
sGeq = sCmpOp "geq" (\x -> x == GT || x == EQ)

sMul, sDiv, sMod, sPow, sAdd, sSub :: Value -> Value -> EvalM Value

sMul = sOp2 $ \u v ->
  case (u,v) of
    (VInt x,  VInt y)  -> sInt (x * y)
    (VReal x, VReal y) -> sReal (x * y)
    _ -> typeError "times" "`(int,int)` or `(real,real)`"

sDiv = sOp2 $ \u v ->
  case (u,v) of
    (VInt x, VInt y)
       | y /= 0    -> sInt (div x y)
       | otherwise -> crash "div" "Division by 0"
    (VReal x, VReal y)
       | y /= 0    -> sReal (x / y)
       | otherwise -> crash "div" "Division by 0"

    _ -> typeError "div" "`(int,int)` or `(real,real)`"

sMod = sOp2 $ \u v ->
  case (u,v) of
    (VInt x, VInt y)
       | y /= 0    -> sInt (mod x y)
       | otherwise -> crash "mod" "Division by 0"
    _ -> typeError "mod" "`(int,Int)`"

sAdd = sOp2 $ \u v ->
  case (u,v) of
    (VInt  x, VInt y)  -> sInt  (x + y)
    (VReal x, VReal y) -> sReal (x + y)
    _                  -> typeError "add" "`(int,int)` or `(real,real)`"


sSub = sOp2 $ \u v ->
  case (u,v) of
    (VInt  x, VInt y)  -> sInt  (x - y)
    (VReal x, VReal y) -> sReal (x - y)
    _                  -> typeError "sub" "`(int,int)` or `(real,real)`"

sPow = sOp2 $ \u v ->
  case (u,v) of
    (VInt  x, VInt y) -> sInt  (x ^ y)
    (VReal x, VInt y) -> sReal (x ^ y)
    _                 -> typeError "pow" "`(int,int)` or `(real,int)`"


-- | Convenient operator used by various boolean functions.
-- The integeras ar the minimum and maximum number of true in the list of value.
sBoolRed :: String -> Integer -> Integer -> [Value] -> EvalM Value
sBoolRed name i j = count 0
  where
  count n as = case as of
                 [] -> pure (VBool (n >= i))
                 VBool b : bs
                   | b -> if n == j then pure (VBool False)
                                    else count (n+1) bs

                 _ -> typeError name "a `bool`"

sITE :: Value -> Value -> Value -> EvalM Value
sITE u v w =
  case u of
    VBool b -> pure (if b then v else w)
    _       -> typeError "ite" "a `bool`"


sReplicate :: Value {-^ Replicate this -} -> Value {-^ Number of times -} ->
              EvalM Value
sReplicate = sOp2 $ \u v ->
  case v of
    VInt x -> sArray (genericReplicate x u)
    _      -> typeError "replicate" "an `int`"

sConcat :: Value -> Value -> EvalM Value
sConcat = sOp2 $ \u v ->
  case (u,v) of
    (VArray xs, VArray ys) -> sArray (xs ++ ys)
    _ -> typeError "concat" "(array,array)"


sSelectField :: Ident -> Value -> EvalM Value
sSelectField f v =
  case v of
    VStruct _ fs ->
      case lookup f fs of
        Just fv -> pure fv
        Nothing -> crash "select-field" "Missing struct field"
    _ -> typeError "select-field" "a struct type."

sSelectIndex :: Value {-^ index -} -> Value {- ^ array -} -> EvalM Value
sSelectIndex = sOp2 $ \i v ->
  case (v,i) of
    (VArray vs, VInt iv)
       | iv < 0      -> outOfBounds
       | otherwise   -> case genericDrop iv vs of
                          []    -> outOfBounds
                          x : _ -> pure x
       where outOfBounds = typeError "sSelectIndex" "array index out of bounds"

    _ -> typeError "select-element" "`(array,int)`"

sSelectSlice :: ArraySlice Value -> Value -> EvalM Value
sSelectSlice sl v =
  case (v, start, end, step) of
    (VArray vs, VInt f, VInt t, VInt s)
      | f >= 0 && t >= f && t < genericLength vs && s > 0 ->
            sArray [ genericIndex vs i | i <- [ f, f + s .. t ] ]
      | otherwise -> crash "get-slice" "Bad arguments"

    _ -> typeError "get-slice" "(array,int,int,int)"
  where
  start = arrayStart sl
  end   = arrayEnd   sl
  step  = case arrayStep sl of
            Just s  -> s
            Nothing -> VInt 1




