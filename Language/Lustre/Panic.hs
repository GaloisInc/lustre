{-# Language TemplateHaskell #-}
module Language.Lustre.Panic (panic) where

import Panic hiding (panic)
import qualified Panic

data Lustre = Lustre

instance PanicComponent Lustre where
  panicComponentName _     = "Lustre"
  panicComponentIssues _   = "https://github.com/GaloisInc/lustre"
  panicComponentRevision   = $useGitRevision

panic :: String -> [String] -> a
panic = Panic.panic Lustre

