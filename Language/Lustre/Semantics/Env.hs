module Language.Lustre.Semantics.Env where

import Data.Map(Map)
import qualified Data.Map as Map

import Language.Lustre.AST
import Language.Lustre.Semantics.Value

-- | Interpretations of free names.
data Env = Env
  { envConsts   :: Map Name Value
  , envConstFun :: Map Name ([Value] -> EvalM [Value])
  , envLocals   :: Map Ident ReactValue
  , envNodes    :: Map Name ([Value] -> [ReactValue] -> EvalM [ReactValue])
  }

lookupLocal :: Env -> Ident -> Maybe ReactValue
lookupLocal env i = Map.lookup i (envLocals env)


