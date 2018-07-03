-- | Additional reading:
-- * http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
-- * https://inst.eecs.berkeley.edu/~ee249/fa07/lecture-lustre-trans.pdf
-- * http://www.cse.unsw.edu.au/~plaice/archive/JAP/P-NYAS92-lustreSemantics.pdf

module Language.Lustre.Semantics where

import Control.Monad(join)

-- Generic streams

data Stream a = Stream a (Stream a)

-- | A constant stream
sConst :: a -> Stream a
sConst f = go
  where go = Stream f go

-- | Apply a function to each element in a stream.
sMap :: (a -> b) -> Stream a -> Stream b
sMap f = go
  where go (Stream a as) = Stream (f a) (go as)

-- | Pair-up the elements of two stream, pointwise.
sZip :: Stream a -> Stream b -> Stream (a,b)
sZip (Stream a as) (Stream b bs) = Stream (a,b) (sZip as bs)

-- | Apply a function to each element in a stream, while treading
-- some state.  (A special case of `mapM` in Haskell).
sMapS :: (a -> s -> (b,s)) -> s -> Stream a -> Stream b
sMapS f = go
  where go s (Stream a xs) = case f a s of
                               (b,s1) -> Stream b (go s1 xs)

--------------------------------------------------------------------------------

-- | Values in Lustre are streams of "steps".
type Value a  = Stream (Step a)

-- | A "step" is either an exisitng element, or an element that has
-- been skipped by a clock.
data Step a   = Emit (Maybe a)    -- ^ 'Nothing' is undefined
              | Skip !Int         -- ^ Clock depth

-- | Literals, sucn as @1@, @True@, etc., as just constant streams.
literal :: a -> Value a
literal a = sConst (Emit (Just a))

-- | Delay all values by one.  This allows us to refer to previous values
-- in a stream.
pre :: Value a -> Value a
pre = Stream (Emit Nothing)

-- | Get the first values from the first stream, and all other values
-- from the second one.   Used to "initialize" the second stream.
fby :: Value a -> Value a -> Value a
fby (Stream a as) (Stream b bs) =
  case (a,b) of
     -- technically, we should continue checking that the clocks
     -- for `as` and `bs` match... perhps?
    (Emit x, Emit _)          -> Stream (Emit x) bs


    (Skip x, Skip y) | x == y -> Stream (Skip x) (fby as bs)
    _                         -> error "fby: clock mismatch"


when :: Value a -> Value Bool -> Value a
when xs ys = sMap step (sZip xs ys)
  where
  step (Emit a, Emit mb) =
    case mb of
      Nothing -> error "undefined clock"
      Just c  -> if c then Emit a else Skip 0
  step (Skip x, Skip y)
    | x == y = Skip (x + 1)
  step _ = error "when: clock mistmach"

current :: Value a -> Value a
current = sMapS step Nothing
  where
  step v def =
    case v of
      Emit a -> (Emit a,   a)
      Skip 0 -> (Emit def, def)
      Skip n -> (Skip (n-1), def)

op1_st :: (a -> b) -> Value a -> Value b
op1_st f = sMap step
  where step (Emit mb) = Emit (f <$> mb)
        step (Skip x)  = Skip x

op2 :: String ->
        (Maybe a -> Maybe b -> Maybe c) -> Value a -> Value b -> Value c

op2 name f xs ys = sMap step (sZip xs ys)
  where
  step (Emit ma, Emit mb) = Emit (f ma mb)
  step (Skip x, Skip y) | x == y = Skip x
  step _  = error (name ++ ": clock mistmach")

op2_st :: String -> (a -> b -> c) -> Value a -> Value b -> Value c
op2_st name f xs ys = op2 name f' xs ys
  where f' ma mb = f <$> ma <*> mb

op2_st' :: String -> (a -> b -> Maybe c) -> Value a -> Value b -> Value c
op2_st' name f xs ys = op2 name f' xs ys
  where f' ma mb = join (f <$> ma <*> mb)


-- data Op1 = Not | Neg | Pre | Current | IntCast | RealCast

lNot :: Value Bool -> Value Bool
lNot = op1_st not

lNeg :: Num a => Value a -> Value a
lNeg = op1_st negate

{-
data Op2 = Fby | And | Or | Xor | Implies | Eq | Neq | Lt | Leq | Gt | Geq
         | Mul | IntDiv | Mod | Div | Add | Sub | Power
         | Replicate | Concat
-}

lAnd :: Value Bool -> Value Bool -> Value Bool
lAnd = op2 "and" step
  where step mbA mB = case (mbA,mB) of
                        (Just False, _)  -> Just False
                        (_, Just False)  -> Just False
                        (Just a, Just b) -> Just (a && b)
                        _                -> Nothing

lOr :: Value Bool -> Value Bool -> Value Bool
lOr xs ys = lNot (lAnd (lNot xs) (lNot ys))

lXOr :: Value Bool -> Value Bool -> Value Bool
lXOr = neq

lImplies :: Value Bool -> Value Bool -> Value Bool
lImplies xs ys = lNot (lAnd (lNot xs) ys)

eq :: Eq a => Value a -> Value a -> Value Bool
eq = op2_st "eq" (==)

neq :: Eq a => Value a -> Value a -> Value Bool
neq xs ys = lNot (eq xs ys)

lt :: Ord a => Value a -> Value a -> Value Bool
lt = op2_st "lt" (<)

leq :: Ord a => Value a -> Value a -> Value Bool
leq = op2_st "leq" (<=)

gt :: Ord a => Value a -> Value a -> Value Bool
gt = op2_st "gt" (>)

geq :: Ord a => Value a -> Value a -> Value Bool
geq = op2_st "geq" (>=)




lAdd :: Num a => Value a -> Value a -> Value a
lAdd = op2_st "add" (+)

lSub :: Num a => Value a -> Value a -> Value a
lSub = op2_st "sub" (-)

lMul :: Num a => Value a -> Value a -> Value a
lMul = op2_st "mul" (*)

lIntDiv :: (Integral a) => Value a -> Value a -> Value a
lIntDiv = op2_st' "div" div'
  where div' _ 0 = Nothing
        div' x y = Just (div x y)

lMod :: (Integral a) => Value a -> Value a -> Value a
lMod = op2_st' "mod" div'
  where div' _ 0 = Nothing
        div' x y = Just (mod x y)

lDiv :: (Fractional a, Eq a) => Value a -> Value a -> Value a
lDiv = op2_st' "/" div'
  where div' _ 0 = Nothing
        div' x y = Just (x / y)







ite :: Value Bool -> Value a -> Value a -> Value a
ite xs ys zs = sMap step (sZip xs (sZip ys zs))
  where step (Emit mb, (Emit x, Emit y)) = Emit $ do b <- mb
                                                     if b then x else y
        step (Skip c1, (Skip c2, Skip c3)) | c1 == c2 && c1 == c3 = Skip c1
        step _ = error "ite: clock mistmach"


-- | Run for some number of steps.
run :: Integer -> Value a -> [Maybe a]
run n (Stream a as)
  | n > 0 = case a of
              Skip _  -> run n as
              Emit mb -> mb : run (n-1) as
  | otherwise = []

