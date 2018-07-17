module Language.Lustre.Semantics.Stream where


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

sJn :: Functor m => Stream m (m a) -> Stream m a
sJn xs =
  Eff $ case xs of
          Stream ma bs -> (`Stream` sJn bs) <$> ma
          Eff m        -> sJn <$> m



-- | Apply a potentially side-effecting function to each element in a stream.
sMapM :: Functor m => (a -> m b) -> Stream m a -> Stream m b
sMapM f = sJn . sMap f

-- | Applay a potentially side-effecting function to each element in a stream.
sForM :: Functor m => Stream m a -> (a -> m b) -> Stream m b
sForM = flip sMapM

-- | Evaluate a stream to weak head-normal form.
sUncons :: Monad m => Stream m a -> m (a, Stream m a)
sUncons (Stream a as) = pure (a, as)
sUncons (Eff m)       = sUncons =<< m

-- | Appply a function to the elements of two stream, pair-wise.
-- Side-effects in the left stream take precedence.
sZipWith :: Monad m => (a -> b -> c) -> Stream m a -> Stream m b -> Stream m c
sZipWith f (Stream a as) (Stream b bs) = Stream (f a b) (sZipWith f as bs)
sZipWith f xs ys = Eff $ do (a,as) <- sUncons xs
                            (b,bs) <- sUncons ys
                            return (Stream (f a b) (sZipWith f as bs))

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
sMapAccum f = go
  where go s (Stream a xs) = case f a s of
                               (b,s1) -> Stream b (go s1 xs)
        go s (Eff mas)     = Eff (go s <$> mas)

