module Language.Lustre.Utils where

import Language.Lustre.Panic
import Language.Lustre.Pretty

-- | Like 'zipWith' except panic if the lists have different lenghts.
zipExact :: (Pretty a, Pretty b) => (a -> b -> c) -> [a] -> [b] -> [c]
zipExact f xs ys
  | length xs == length ys = zipWith f xs ys
  | otherwise = panic "zipExact"
                  $ "MISMATCH"
                  : "--- LHS: ---"
                  : map showPP xs
                  ++ ("--- RHS: ---" : map showPP ys)

