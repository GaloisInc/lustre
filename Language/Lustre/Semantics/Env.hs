module Language.Lustre.Semantics.Env where

import Data.Map(Map)

import Language.Lustre.AST
import Language.Lustre.Semantics.Value

-- | Interpretations of free names.
data Env = Env
  { envConsts   :: Map Name Value
  , envConstFun :: Map Name ([Value] -> EvalM [Value])
  , envVars     :: Map Name ReactValue
  , envNodes    :: Map Name ([Value] -> [ReactValue] -> EvalM [ReactValue])
  }


