module Language.Lustre.Utils where

import Language.Lustre.Panic

-- | Like 'zipWith' except panic if the lists have different lenghts.
zipExact :: (a -> b -> c) -> [a] -> [b] -> [c]
zipExact f as bs =
  case (as, bs) of
    ([],[])           -> []
    (x : xs, y : ys)  -> f x y : zipExact f xs ys
    ([], _)           -> panic "zipExact" [ "More on the right." ]
    _                 -> panic "zipExact" [ "More on the left."  ]

