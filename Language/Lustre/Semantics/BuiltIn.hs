module Language.Lustre.Semantics.BuiltIn
  ( -- * Static

    -- * Constants
    sInt, sReal, sBool, sNil

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


    -- * Reactive
  , dNil, dBool, dInt, dReal
  , op1
  , op2
  , opN
  , dArray

  , ite
  , when
  , selectOp

  ) where

import Data.List(genericReplicate,genericDrop,genericIndex,genericLength)

import Language.Lustre.AST
import Language.Lustre.Semantics.Stream
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

sNil :: EvalM Value
sNil = pure VNil

sNot :: Value -> EvalM Value
sNot v =
  case v of
    VBool x -> sBool (not x)
    VNil    -> sNil
    _       -> typeError "not" "a `bool`"

sNeg :: Value -> EvalM Value
sNeg v =
  case v of
    VInt x  -> sInt (negate x)
    VReal x -> sReal (negate x)
    VNil    -> sNil
    _       -> typeError "uminus" "a `real` or a `number`"

sReal2Int :: Value -> EvalM Value
sReal2Int v =
  case v of
    VReal x -> sInt (truncate x)
    VNil    -> sNil
    _       -> typeError "real2int" "a `real`"

sInt2Real :: Value -> EvalM Value
sInt2Real v =
  case v of
    VInt x -> sReal (fromInteger x)
    VNil   -> sNil
    _      -> typeError "int2real" "an `int`"


sOp2 :: (Value -> Value -> EvalM Value) -> Value -> Value -> EvalM Value
sOp2 f u v =
  case (u,v) of
    (VNil,_) -> sNil
    (_,VNil) -> sNil
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
    VNil    -> sNil
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
    VNil -> sNil
    VStruct _ fs ->
      case lookup f fs of
        Just fv -> pure fv
        Nothing -> crash "select-field" "Missing struct field"
    _ -> typeError "select-field" "a struct type."

sSelectIndex :: Value {-^ index -} -> Value {- ^ array -} -> EvalM Value
sSelectIndex = sOp2 $ \i v ->
  case (v,i) of
    (VArray vs, VInt iv)
       | iv < 0      -> pure VNil
       | otherwise   -> case genericDrop iv vs of
                          []    -> pure VNil
                          x : _ -> pure x

    _ -> typeError "select-element" "`(array,int)`"

sSelectSlice :: ArraySlice Value -> Value -> EvalM Value
sSelectSlice sl v =
  case (v, start, end, step) of
    (VNil,_,_,_) -> sNil
    (_,VNil,_,_) -> sNil
    (_,_,VNil,_) -> sNil
    (_,_,_,VNil) -> sNil

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





--------------------------------------------------------------------------------
-- Reactive

dNil :: ReactValue
dNil = defineConst VNil

dInt :: Integer -> ReactValue
dInt = defineConst . VInt

dReal :: Rational -> ReactValue
dReal = defineConst . VReal

dBool :: Bool -> ReactValue
dBool = defineConst . VBool

dArray :: [ReactValue] -> EvalM ReactValue
dArray vs = defineOpN "array" vs (pure . VArray)

op1 :: Op1 -> ReactValue -> EvalM ReactValue
op1 op rv =
  case op of

    Not       -> defineOp1 "not"      rv sNot
    Neg       -> defineOp1 "uminus"   rv sNeg

    IntCast   -> defineOp1 "real2int" rv sReal2Int
    RealCast  -> defineOp1 "int2real" rv sInt2Real

    Pre       -> pure (Stream (Emit VNil) (pure rv))
    Current   -> pure (current rv)


op2 :: Op2 -> ReactValue -> ReactValue -> EvalM ReactValue
op2 op xs ys =
  case op of

    Fby     -> pure (fby xs ys)

    And     -> defineOp2 "and" xs ys sAnd
    Or      -> defineOp2 "or"  xs ys sOr
    Xor     -> defineOp2 "xor" xs ys sXor
    Implies -> defineOp2 "implies" xs ys sImplies

    Eq      -> defineOp2 "eq"  xs ys sEq
    Neq     -> defineOp2 "neq" xs ys sNeq

    Lt      -> defineOp2 "lt"  xs ys sLt
    Leq     -> defineOp2 "leq" xs ys sLeq
    Gt      -> defineOp2 "gt"  xs ys sGt
    Geq     -> defineOp2 "geq" xs ys sGeq

    Mul     -> defineOp2 "mul" xs ys sMul
    Mod     -> defineOp2 "mod" xs ys sMod
    Div     -> defineOp2 "div" xs ys sDiv
    Add     -> defineOp2 "add" xs ys sAdd
    Sub     -> defineOp2 "sub" xs ys sSub
    Power   -> defineOp2 "pow" xs ys sPow

    Replicate -> defineOp2 "replicate" xs ys sReplicate
    Concat    -> defineOp2 "concat" xs ys sConcat


opN :: OpN -> [ReactValue] -> EvalM ReactValue
opN op rv =
  case op of
    AtMostOne -> defineOpN "at-most-one" rv (sBoolRed "at-most-one" 0 1)
    Nor       -> defineOpN "nor"         rv (sBoolRed "nor" 0 0)



selectOp :: (Value -> EvalM Value) -> ReactValue -> EvalM ReactValue
selectOp sel rv = defineOp1 "select" rv sel


-- | If-then-else
ite :: ReactValue -> ReactValue -> ReactValue -> EvalM ReactValue
ite xs ys zs = sSequence (sZipWith step xs (sZip ys zs))
  where
  step x (y,z) =
    case (x,y,z) of
      (Emit VNil,      Emit _, Emit _) -> pure (Emit VNil)
      (Emit (VBool b), Emit t, Emit e) -> pure (Emit (if b then t else e))
      (Emit _,         Emit _, Emit _) ->
          crash "ite" "Type error: expected bool"
      (Skip b,         Skip t, Skip e) | b == t && b == e -> pure (Skip b)
      _ -> crash "ite" "clock mismatch"



-- | Get the first values from the first stream, and all other values
-- from the second one.   Used to "initialize" the second stream.
fby :: ReactValue -> ReactValue -> ReactValue
fby (Stream x _) (Stream _ ys) = Stream x ys


-- | The `when` operator. The second argument should be booleans.
when :: ReactValue -> ReactValue -> EvalM ReactValue
when xs ys = sSequence (sZipWith step xs ys)
  where
  step (Emit a) (Emit mb) =
    case mb of
      VBool c -> pure (if c then Emit a else Skip 0)
      _       -> crash "when" "Unexpected clock value"

  step (Skip x) (Skip y)
    | x == y = pure (Skip (x + 1))

  step _ _ = crash "when" "clock mistmach"


-- | The current operator
current :: ReactValue -> ReactValue
current = sMapAccum step VNil
  where
  step v def =
    case v of
      Emit a -> (Emit a,     a)
      Skip 0 -> (Emit def,   def)
      Skip n -> (Skip (n-1), def)



--------------------------------------------------------------------------------
data OpNState a = Start | Ok [a] | EmitNil | Skipping !Int | Error String




-- | The semantics for an N-ary operators.
--    * The values must all run on the same clock
--    * If any of the values is Nil, the result is Nil
defineOpN :: String ->
             [ReactValue] -> ([Value] -> EvalM Value) -> EvalM ReactValue
defineOpN name xs f = sMapM mkVal (sFold cons Start xs)
  where
  mkVal s             = case s of
                          Start       -> Emit <$> f []
                          Ok vs       -> Emit <$> f vs
                          EmitNil     -> pure (Emit VNil)
                          Skipping n  -> pure (Skip n)
                          Error e     -> crash name e

  cons (Skip n) s     = case s of
                          Start               -> Skipping n
                          Skipping i | i == n -> Skipping i
                          Error e             -> Error e
                          _                   -> Error "clock mistmatch"

  cons (Emit VNil) s  = case s of
                          Error e    -> Error e
                          Skipping _ -> Error "clock mistmath"
                          _          -> EmitNil

  cons (Emit v) s     = case s of
                          Error e    -> Error e
                          Skipping _ -> Error "clock mistmath"
                          EmitNil    -> EmitNil
                          Start      -> Ok [v]
                          Ok vs      -> Ok (v:vs)

defineConst :: Value -> ReactValue
defineConst v = sConst (Emit v)


defineOp1 :: String -> ReactValue -> (Value -> EvalM Value) -> EvalM ReactValue
defineOp1 name xs f = defineOpN name [xs] $ \ ~[as] -> f as

defineOp2 :: String ->
       ReactValue -> ReactValue ->
       (Value -> Value -> EvalM Value) ->
       EvalM ReactValue
defineOp2 name xs ys f = defineOpN name [xs,ys] $ \ ~[as,bs] -> f as bs



