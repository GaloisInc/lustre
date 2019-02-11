-- | Process a collection of declarations all the way.
module Language.Lustre.Driver where

import qualified Data.Map as Map

import Language.Lustre.AST
import Language.Lustre.Monad
import Language.Lustre.Transform.OrderDecls
import Language.Lustre.TypeCheck
import Language.Lustre.Transform.NoStatic
import Language.Lustre.Transform.NoStruct
import Language.Lustre.Transform.Inline


quickDeclsToCore :: [TopDecl] -> LustreM todo
quickDeclsToCore ds =
  do ds1 <- quickOrderTopDecl ds
     quickCheckDecls ds1 -- XXX: only if enabled
     (csMap,ds2) <- noConst ds1
     let nosIn = NosIn
                   { nosiStructs   = Map.empty
                   , nosiCallSites = csMap
                   }
     (ds3,nosOut) <- noStruct nosIn ds2
     (rens,ds4)   <- inlineCalls [] ds3
     undefined

