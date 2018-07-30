module Language.Lustre.Semantics.Stream where

import Control.Monad(liftM2)


-- | Effectful stream, in WHNF.
data Stream m a     = Stream a (m (Stream m a))

-- | A constant stream
sConst :: Monad m => a -> Stream m a
sConst f = go
  where go = Stream f (pure go)

-- | Apply a function to each element in a stream.
sMap :: Monad m => (a -> b) -> Stream m a -> Stream m b
sMap f (Stream a xs) = Stream (f a) (sMap f <$> xs)

-- | Appply a function to the elements of two stream, pair-wise.
-- Side-effects in the left stream take precedence.
sZipWith :: Monad m => (a -> b -> c) -> Stream m a -> Stream m b -> Stream m c
sZipWith f (Stream a as) (Stream b bs) =
  Stream (f a b) (liftM2 (sZipWith f) as bs)

-- | Pair-up the elements of two streams, pair-wise.
sZip :: Monad m => Stream m a -> Stream m b -> Stream m (a,b)
sZip = sZipWith (,)

-- | Fold the elements of a bunch of streams pointwise.
sFold :: Monad m => (a -> b -> b) -> b -> [Stream m a] -> Stream m b
sFold cons nil xs =
  case xs of
    []     -> sConst nil
    a : as -> sZipWith cons a (sFold cons nil as)

-- | Apply a function to each element in a stream, while treading
-- some state.  (A special case of `mapM` in Haskell).
sMapAccum :: Functor m => (a -> s -> (b,s)) -> s -> Stream m a -> Stream m b
sMapAccum f s (Stream a xs) =
  case f a s of
    (b,s1) -> Stream b (sMapAccum f s1 <$> xs)


sSequence :: Monad m => Stream m (m a) -> m (Stream m a)
sSequence (Stream mx xs) =
  do x <- mx
     return (Stream x (sSequence =<< xs))

-- | Apply a potentially side-effecting function to each element in a stream.
sMapM :: Monad m => (a -> m b) -> Stream m a -> m (Stream m b)
sMapM f = sSequence . sMap f

-- | Applay a potentially side-effecting function to each element in a stream.
sForM :: Monad m => Stream m a -> (a -> m b) -> m (Stream m b)
sForM = flip sMapM


