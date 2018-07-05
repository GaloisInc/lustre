-- | Additional reading:
-- * http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
-- * https://inst.eecs.berkeley.edu/~ee249/fa07/lecture-lustre-trans.pdf
-- * http://www.cse.unsw.edu.au/~plaice/archive/JAP/P-NYAS92-lustreSemantics.pdf

module Language.Lustre.Semantics where

import Control.Monad(join)
import Data.Map(Map)
import qualified Data.Map as Map

import Language.Lustre.AST

-- Generic streams

-- | Stream with support for side effects.
-- @Eff (return x) == x@
data Stream m a = Stream a (Stream m a)
                | Eff (m (Stream m a))

-- | A constant stream
sConst :: a -> Stream m a
sConst f = go
  where go = Stream f go

-- | Apply a function to each element in a stream.
sMap :: Functor m => (a -> b) -> Stream m a -> Stream m b
sMap f = go
  where go (Stream a as) = Stream (f a) (go as)
        go (Eff m)       = Eff (go <$> m)

-- | Apply a potentially side-effecting function to each element in a stream.
sMapM :: Functor m => (a -> m b) -> Stream m a -> Stream m b
sMapM f = go
  where go (Stream a as) = Eff ((`Stream` go as) <$> f a)
        go (Eff m)       = Eff (go <$> m)

sForM :: Functor m => Stream m a -> (a -> m b) -> Stream m b
sForM = flip sMapM

-- | Evaluate a stream to weak head-normal form.
sWHNF :: Monad m => Stream m a -> m (a, Stream m a)
sWHNF (Stream a as) = pure (a, as)
sWHNF (Eff m)       = sWHNF =<< m


-- | Pair-up the elements of two stream, pointwise.
-- Side-effects in the left stream take precedence.
sZip :: Monad m => Stream m a -> Stream m b -> Stream m (a,b)
sZip (Stream a as) (Stream b bs) = Stream (a,b) (sZip as bs)
sZip xs ys                       = Eff $ do (a,as) <- sWHNF xs
                                            (b,bs) <- sWHNF ys
                                            return (Stream (a,b) (sZip as bs))

-- | Apply a function to each element in a stream, while treading
-- some state.  (A special case of `mapM` in Haskell).
sMapS :: Functor m => (a -> s -> (b,s)) -> s -> Stream m a -> Stream m b
sMapS f = go
  where go s (Stream a xs) = case f a s of
                               (b,s1) -> Stream b (go s1 xs)
        go s (Eff mas)     = Eff (go s <$> mas)

--------------------------------------------------------------------------------

-- | The universe of basic values.
-- These are the values used for a specific time instance.
data Value    = VInt  !Integer
              | VBool !Bool
              | VReal !Rational
              | VNil
              | VEnum !Name !Ident                -- ^ Type, value
              | VStruct !Name ![(Ident,Value)]    -- ^ Type, fields
              | VArray ![Value]
                deriving Show

-- | A reactive value represents the evolution of a basic value over time,
-- as driven by a clock.
type ReactValue = Stream EvalM Step


-- | A "step" is either an exisitng element,
-- or an element that has been skipped by a clock.
data Step     = Emit !Value   -- ^ An existing element.
              | Skip !Int     -- ^ Skipped by clock at the given depth
                              -- (0 is the current clock)

-- | Interpretations of free names.
data Env = Env
  { freeVars    :: Map Name ReactValue
  , externNodes :: Map Name () -- XXX
  }

type EvalM = Either Error
type Error = String

crash :: String -> String -> EvalM a
crash x y = Left (x ++ ": " ++ y)
--------------------------------------------------------------------------------


evalLiteral :: Literal -> ReactValue
evalLiteral l = rv
  where
  v = case l of
        Int n  -> VInt n
        Real r -> VReal r
        Bool b -> VBool b

  rv = Stream (Emit v) rv


evalExpr :: Env -> Expression -> ReactValue
evalExpr env expr =
  case expr of
    ERange _ e -> evalExpr env e

    Lit l -> evalLiteral l
    EOp1 op e ->
      let rv = evalExpr env e
      in case op of

           Not -> op1 rv $ \v -> case v of
                                  VBool x -> pure $ VBool $ not x
                                  _       -> crash "not" "expected a Bool"

           Neg -> op1 rv $ \v -> case v of
                                   VInt x  -> pure $ VInt $ negate x
                                   VReal x -> pure $ VReal $ negate x
                                   _       -> crash "neg" "expected a number"

           Pre     -> Stream (Emit VNil) rv
           Current -> current rv
           IntCast -> op1 rv $ \v -> case v of
                                       VReal x -> pure $ VInt $ truncate x
                                       _       -> crash "int" "expected a real"
           RealCast -> op1 rv $ \v -> case v of
                                        VInt x -> pure $ VReal $ fromInteger x
                                        _      -> crash "real" "expected an int"

    EOp2 e1 op e2 ->
      let xs = evalExpr env e1
          ys = evalExpr env e2
      in case op of

           Fby -> fby xs ys

           And ->
             op2 "and" xs ys $ \v1 v2 ->
             case (v1,v2) of
               (VBool x, VBool y) -> pure $ VBool $ x && y
               _ -> crash "and" "Expected booleans"

           Or ->
             op2 "or" xs ys $ \v1 v2 ->
             case (v1,v2) of
               (VBool x, VBool y) -> pure $ VBool $ x || y
               _ -> crash "or" "Expected booleans"

           Xor ->
             op2 "xor" xs ys $ \v1 v2 ->
             case (v1,v2) of
               (VBool x, VBool y) -> pure $ VBool $ x /= y
               _ -> crash "xor" "Expected booleans"

           Implies ->
             op2 "implies" xs ys $ \v1 v2 ->
              case (v1,v2) of
                (VBool x, VBool y) -> pure $ VBool $ not x || y
                _ -> crash "implies" "Expected booleans"







        Fby | And | Or | Xor | Implies | Eq | Neq | Lt | Leq | Gt | Geq



-- | Delay all values by one.  This allows us to refer to previous values
-- in a stream.
pre :: ReactValue -> ReactValue
pre = Stream (Emit VNil)

-- | Get the first values from the first stream, and all other values
-- from the second one.   Used to "initialize" the second stream.
fby :: ReactValue -> ReactValue -> ReactValue
fby xs ys = sMapS step False (sZip xs ys)
  where step (a,b) initialized = (if initialized then b else a, True)


when :: ReactValue -> ReactValue -> ReactValue
when xs ys = sMapM step (sZip xs ys)
  where
  step (Emit a, Emit mb) =
    case mb of
      VBool c -> pure (if c then Emit a else Skip 0)
      _       -> crash "when" "Unexpected clock value"

  step (Skip x, Skip y)
    | x == y = pure (Skip (x + 1))

  step _ = crash "when" "clock mistmach"

current :: ReactValue -> ReactValue
current = sMapS step VNil
  where
  step v def =
    case v of
      Emit a -> (Emit a,   a)
      Skip 0 -> (Emit def, def)
      Skip n -> (Skip (n-1), def)

op1 :: ReactValue -> (Value -> EvalM Value) -> ReactValue
op1 xs f = sMapM f' xs
  where f' step = case step of
                    Emit VNil -> pure (Emit VNil)
                    Emit a    -> Emit <$> f a
                    Skip n    -> pure (Skip n)

op2 :: String ->
       ReactValue -> ReactValue ->
      (Value -> Value -> EvalM Value) -> ReactValue
op2 name xs ys f = sMapM f' (sZip xs ys)
  where
  f' (Emit VNil, _)      = pure (Emit VNil)
  f' (_, Emit VNil)      = pure (Emit VNil)
  f' (Emit ma, Emit mb)  = Emit <$> f ma mb
  f' (Skip x, Skip y) | x == y = pure (Skip x)
  f' _                   = crash name "clock mistmach"

{-
op2_st :: String -> (a -> b -> c) -> TValue a -> TValue b -> TValue c
op2_st name f xs ys = op2 name f' xs ys
  where f' ma mb = f <$> ma <*> mb

op2_st' :: String -> (a -> b -> Maybe c) -> TValue a -> TValue b -> TValue c
op2_st' name f xs ys = op2 name f' xs ys
  where f' ma mb = join (f <$> ma <*> mb)


-- data Op1 = Not | Neg | Pre | Current | IntCast | RealCast

lNot :: TValue Bool -> TValue Bool
lNot = op1_st not

lNeg :: Num a => TValue a -> TValue a
lNeg = op1_st negate

{-
data Op2 = Fby | And | Or | Xor | Implies | Eq | Neq | Lt | Leq | Gt | Geq
         | Mul | IntDiv | Mod | Div | Add | Sub | Power
         | Replicate | Concat
-}

lAnd :: TValue Bool -> TValue Bool -> TValue Bool
lAnd = op2 "and" step
  where step mbA mB = case (mbA,mB) of
                        (Just False, _)  -> Just False
                        (_, Just False)  -> Just False
                        (Just a, Just b) -> Just (a && b)
                        _                -> Nothing

lOr :: TValue Bool -> TValue Bool -> TValue Bool
lOr xs ys = lNot (lAnd (lNot xs) (lNot ys))

lXOr :: TValue Bool -> TValue Bool -> TValue Bool
lXOr = neq

lImplies :: TValue Bool -> TValue Bool -> TValue Bool
lImplies xs ys = lNot (lAnd (lNot xs) ys)

eq :: Eq a => TValue a -> TValue a -> TValue Bool
eq = op2_st "eq" (==)

neq :: Eq a => TValue a -> TValue a -> TValue Bool
neq xs ys = lNot (eq xs ys)

lt :: Ord a => TValue a -> TValue a -> TValue Bool
lt = op2_st "lt" (<)

leq :: Ord a => TValue a -> TValue a -> TValue Bool
leq = op2_st "leq" (<=)

gt :: Ord a => TValue a -> TValue a -> TValue Bool
gt = op2_st "gt" (>)

geq :: Ord a => TValue a -> TValue a -> TValue Bool
geq = op2_st "geq" (>=)




lAdd :: Num a => TValue a -> TValue a -> TValue a
lAdd = op2_st "add" (+)

lSub :: Num a => TValue a -> TValue a -> TValue a
lSub = op2_st "sub" (-)

lMul :: Num a => TValue a -> TValue a -> TValue a
lMul = op2_st "mul" (*)

lIntDiv :: (Integral a) => TValue a -> TValue a -> TValue a
lIntDiv = op2_st' "div" div'
  where div' _ 0 = Nothing
        div' x y = Just (div x y)

lMod :: (Integral a) => TValue a -> TValue a -> TValue a
lMod = op2_st' "mod" div'
  where div' _ 0 = Nothing
        div' x y = Just (mod x y)

lDiv :: (Fractional a, Eq a) => TValue a -> TValue a -> TValue a
lDiv = op2_st' "/" div'
  where div' _ 0 = Nothing
        div' x y = Just (x / y)







ite :: TValue Bool -> TValue a -> TValue a -> TValue a
ite xs ys zs = sMap step (sZip xs (sZip ys zs))
  where step (Emit mb, (Emit x, Emit y)) = Emit $ do b <- mb
                                                     if b then x else y
        step (Skip c1, (Skip c2, Skip c3)) | c1 == c2 && c1 == c3 = Skip c1
        step _ = error "ite: clock mistmach"


-- | Run for some number of steps.
run :: Integer -> TValue a -> [Maybe a]
run n (Stream a as)
  | n > 0 = case a of
              Skip _  -> run n as
              Emit mb -> mb : run (n-1) as
  | otherwise = []
-}

