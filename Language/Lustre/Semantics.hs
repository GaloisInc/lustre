-- | Additional reading:
-- * http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
-- * https://inst.eecs.berkeley.edu/~ee249/fa07/lecture-lustre-trans.pdf
-- * http://www.cse.unsw.edu.au/~plaice/archive/JAP/P-NYAS92-lustreSemantics.pdf
module Language.Lustre.Semantics
  ( Value(..)
  , EvalM
  , Error
  , ReactValue
  , Step(..)
  , Env(..)
  , evalExpr
  )
  where

import Data.List(genericReplicate,genericDrop)
import Data.Maybe(fromMaybe)
import Data.Map(Map)
import qualified Data.Map as Map

import Language.Lustre.AST
import Language.Lustre.Semantics.Stream

-- | The universe of basic values.
-- These are the values used for a specific time instance.
data Value    = VInt    !Integer
              | VBool   !Bool
              | VReal   !Rational
              | VNil
              | VEnum   !Name !Ident              -- ^ Type, value
              | VStruct !Name ![(Ident,Value)]    -- ^ Type, fields
              | VTuple  ![Value]
              | VArray  ![Value]
                deriving Show

instance Eq Value where
  x == y =
    case (x,y) of
      (VInt a,  VInt b)        -> a == b
      (VBool a, VBool b)       -> a == b
      (VReal a, VReal b)       -> a == b
      (VEnum t1 a, VEnum t2 b) -> t1 == t2 && a == b
      (VTuple as, VTuple bs)   -> cmpArr as bs    -- Reuse, since we are untyped
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
              | Skip !Int     -- ^ Skipped by clock at the given depth
                              -- (0 is the current clock)

-- | Interpretations of free names.
data Env = Env
  { freeVars    :: Map Name ReactValue
  , externNodes :: Map Name () -- XXX
  , enumTypes   :: Map Name [ Ident ]

  }


crash :: String -> String -> EvalM a
crash x y = Left (x ++ ": " ++ y)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------


evalLiteral :: Literal -> ReactValue
evalLiteral l = sConst $ Emit $ case l of
                                  Int n  -> VInt n
                                  Real r -> VReal r
                                  Bool b -> VBool b


evalExpr :: Env -> Expression -> ReactValue
evalExpr env expr =

  case expr of
    ERange _ e -> evalExpr env e

    Lit l -> evalLiteral l

    IfThenElse b t e -> ite (evalExpr env b) (evalExpr env t) (evalExpr env e)

    WithThenElse {} -> error "[evalExpr] XXX: WithThenElse"
    When {}         -> error "[evalExpr] XXX: When"
    Merge {}        -> error "[evalExpr] XXX: Merge"
    Var {}          -> error "[evalExpr] XXX: Var"
    CallPos {}      -> error "[evalExpr] XXX: CallPos"
    CallNamed {}    -> error "[evalExpr] XXX: CallNamed"

    Tuple es -> defineOpN "tuple" (map (evalExpr env) es) (pure . VTuple)
    Array es -> defineOpN "array" (map (evalExpr env) es) (pure . VArray)

    Select e sel -> selectOp evalSel (evalExpr env e)
      where evalSel = case sel of
                        SelectField f -> SelectField f
                        SelectElement i -> SelectElement (evalExpr env i)
                        SelectSlice s -> SelectSlice
                          ArraySlice { arrayStart = evalExpr env (arrayStart s)
                                     , arrayEnd   = evalExpr env (arrayEnd s)
                                     , arrayStep  = evalExpr env <$> arrayStep s
                                     }

    EOpN op es    -> opN op (map (evalExpr env) es)
    EOp1 op e     -> op1 op (evalExpr env e)
    EOp2 e1 op e2 -> op2 op (evalExpr env e1) (evalExpr env e2)



op1 :: Op1 -> ReactValue -> ReactValue
op1 op rv =
  case op of

    Not -> defineOp1 "not" rv $ \v ->
      case v of
        VBool x -> pure $ VBool $ not x
        _       -> crash "not" "expected a Bool"

    Neg -> defineOp1 "neg" rv $ \v ->
      case v of
        VInt x  -> pure $ VInt  $ negate x
        VReal x -> pure $ VReal $ negate x
        _       -> crash "neg" "expected a number"

    Pre     -> Stream (Emit VNil) rv
    Current -> current rv
    IntCast -> defineOp1 "int-cast" rv $ \v ->
      case v of
        VReal x -> pure $ VInt $ truncate x
        _       -> crash "int" "expected a real"

    RealCast -> defineOp1 "real-cast" rv $ \v ->
      case v of
        VInt x -> pure $ VReal $ fromInteger x
        _      -> crash "real" "expected an int"


op2 :: Op2 -> ReactValue -> ReactValue -> ReactValue
op2 op xs ys =
  case op of

    Fby -> fby xs ys

    And -> defineOp2 "and" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VBool x, VBool y) -> vBool (x && y)
        _                  -> crash "and" "Expected booleans"

    Or -> defineOp2 "or" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VBool x, VBool y) -> vBool (x || y)
        _ -> crash "or" "Expected booleans"

    Xor -> defineOp2 "xor" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VBool x, VBool y) -> vBool (x /= y)
        _ -> crash "xor" "Expected booleans"

    Implies -> defineOp2 "implies" xs ys $ \v1 v2 ->
       case (v1,v2) of
         (VBool x, VBool y) -> vBool (not x || y)
         _ -> crash "implies" "Expected booleans"

    Eq -> defineOp2 "eq" xs ys $ \v1 v2 ->
       vBool (v1 == v2)

    Neq -> defineOp2 "neq" xs ys $ \v1 v2 ->
       vBool (v1 /= v2)

    Lt -> defineOp2 "lt" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vBool (a < b)
        (VReal a, VReal b) -> vBool (a < b)
        _ -> crash "lt" "Not a numeric type"

    Leq -> defineOp2 "leq" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vBool (a <= b)
        (VReal a, VReal b) -> vBool (a <= b)
        _ -> crash "leq" "Not a numeric type"

    Gt -> defineOp2 "gt" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vBool (a > b)
        (VReal a, VReal b) -> vBool (a > b)
        _ -> crash "lt" "Not a numeric type"

    Geq -> defineOp2 "geq" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vBool (a >= b)
        (VReal a, VReal b) -> vBool (a >= b)
        _ -> crash "leq" "Not a numeric type"

    Mul -> defineOp2 "mul" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vInt  (a * b)
        (VReal a, VReal b) -> vReal (a * b)
        _ -> crash "mul" "Not a numeric type"

    IntDiv -> defineOp2 "int_div" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)
           | b /= 0    -> vInt (div a b)
           | otherwise -> crash "int_div" "Division by 0"
        _ -> crash "mul" "Not a numeric type"

    Mod -> defineOp2 "mod" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)
           | b /= 0    -> vInt (mod a b)
           | otherwise -> crash "mod" "Division by 0"
        _ -> crash "mod" "Not a numeric type"

    Div -> defineOp2 "div" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VReal a, VReal b)
           | b /= 0    -> vReal (a / b)
           | otherwise -> crash "int_div" "Division by 0"
        _ -> crash "div" "Expected inputs of type real."

    Add -> defineOp2 "add" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vInt  (a + b)
        (VReal a, VReal b) -> vReal (a + b)
        _ -> crash "mul" "Not a numeric type"

    Sub -> defineOp2 "sub" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vInt  (a - b)
        (VReal a, VReal b) -> vReal (a - b)
        _ -> crash "mul" "Not a numeric type"

    Power -> defineOp2 "pow" xs ys $ \v1 v2 ->
      case (v1,v2) of
        (VInt  a, VInt b)  -> vInt  (a ^ b)
        (VReal a, VInt b)  -> vReal (a ^ b)
        _ -> crash "pow" "Not a numeric type or non-integral power"

    Replicate -> defineOp2 "replicate" xs ys $ \v1 v2 ->
      case v2 of
        VInt a -> vArray (genericReplicate a v1)
        _      -> crash "replicate" "Non-integral replicate amount."

    Concat -> defineOp2 "concat" xs ys $ \v1 v2 ->
       case (v1,v2) of
         (VArray as, VArray bs) -> vArray (as ++ bs)
         _ -> crash "concat" "Inputs are not arrays."

  where
  vBool x  = pure (VBool x)
  vReal x  = pure (VReal x)
  vInt x   = pure (VInt x)
  vArray x = pure (VArray x)


opN :: OpN -> [ReactValue] -> ReactValue
opN op rv =
  case op of
    AtMostOne -> defineOpN "at-most-one" rv (boolred "at-most-one" 0 1)
    Nor       -> defineOpN "nor"         rv (boolred "nor" 0 0)



selectOp :: Selector ReactValue -> ReactValue -> ReactValue
selectOp sel rv =
  case sel of

    SelectField f -> defineOp1 "get-field" rv $ \v ->
      case v of
        VStruct _ fs ->
           case lookup f fs of
             Just fv -> pure fv
             Nothing -> crash "select-field" "Missing struct field"
        _ -> crash "select-field" "Select from non-struct"

    SelectElement ei -> defineOp2 "get-element" rv ei $ \v i ->
      case (v,i) of
        (VArray vs, VInt iv)
           | iv < 0      -> pure VNil
           | otherwise   -> case genericDrop iv vs of
                              []    -> pure VNil
                              x : _ -> pure x
        _ -> crash "select-element" "Expected array and integer"

    SelectSlice sl ->
      let start = arrayStart sl
          end   = arrayEnd   sl
          step  = case arrayStep sl of
                    Just s -> s
                    Nothing -> sMap one start
          one x = case x of
                    Skip n -> Skip n
                    Emit _ -> Emit (VInt 1)
      in defineOpN "get-slice" [rv,start,end,step] $ \ ~[arr,from,to,stp] ->
           case (arr,from,to,stp) of
             (VArray vs, VInt f, VInt t, VInt s)
               | f > 0 && t >= 0 && s > 0 ->
                 let el i = case genericDrop i vs of
                              []    -> VNil
                              v : _ -> v
                 in pure (VArray [ el i | i <- [ f, f + s .. t ] ])

             _ -> crash "get-slice" "Bad arguments"




-- | If-then-else
ite :: ReactValue -> ReactValue -> ReactValue -> ReactValue
ite xs ys zs = sJn (sZipWith step xs (sZip ys zs))
  where
  step x (y,z) =
    case (x,y,z) of
      (Emit VNil,      Emit _, Emit _) -> pure (Emit VNil)
      (Emit (VBool b), Emit t, Emit e) -> pure (Emit (if b then t else e))
      (Emit _,         Emit _, Emit _) ->
          crash "ite" "Type error: expected bool"
      (Skip b,         Skip t, Skip e) | b == t && b == e -> pure (Skip b)
      _ -> crash "ite" "clock mismatch"



-- | Convenient operator used by various boolean functions.
boolred :: String -> Integer -> Integer -> [Value] -> EvalM Value
boolred name i j = count 0
  where
  count n as = case as of
                 [] -> pure (VBool (n >= i))
                 VBool b : bs
                   | b -> if n == j then pure (VBool False)
                                    else count (n+1) bs

                 _ -> crash name "Expected a boolean input"

-- | Get the first values from the first stream, and all other values
-- from the second one.   Used to "initialize" the second stream.
fby :: ReactValue -> ReactValue -> ReactValue
fby xs ys = sMapAccum step False (sZip xs ys)
  where step (a,b) initialized = (if initialized then b else a, True)


-- | The `when` operator. The second argument should be booleans.
when :: ReactValue -> ReactValue -> ReactValue
when xs ys = sJn (sZipWith step xs ys)
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
defineOpN :: String -> [ReactValue] -> ([Value] -> EvalM Value) -> ReactValue
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
                          _                   -> Error "clock mistmath"

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


defineOp1 :: String -> ReactValue -> (Value -> EvalM Value) -> ReactValue
defineOp1 name xs f = defineOpN name [xs] $ \ ~[as] -> f as

defineOp2 :: String ->
       ReactValue -> ReactValue ->
       (Value -> Value -> EvalM Value) ->
       ReactValue
defineOp2 name xs ys f = defineOpN name [xs,ys] $ \ ~[as,bs] -> f as bs



{-

-- | Run for some number of steps.
run :: Integer -> TValue a -> [Maybe a]
run n (Stream a as)
  | n > 0 = case a of
              Skip _  -> run n as
              Emit mb -> mb : run (n-1) as
  | otherwise = []
-}

