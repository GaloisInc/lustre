-- | Desugar a node from source-level Lustre into core-lustre
module Language.Lustre.Transform.Desugar where

import Control.Monad(msum)

import qualified Language.Lustre.AST as P
import qualified Language.Lustre.Core as C
import Language.Lustre.Pretty(pp)

import Language.Lustre.Transform.OrderDecls(orderTopDecls)
import Language.Lustre.Transform.NoStatic(quickNoConst)
import Language.Lustre.Transform.NoStruct(quickNoStruct)
import Language.Lustre.Transform.Inline(quickInlineCalls)
import Language.Lustre.Transform.ToCore(evalNodeDecl, getEnumInfo)

import Language.Lustre.Panic


-- | Given the declarations from a single module, and the name of a
-- node, compute the node in Core Lustre form.
-- XXX: This could use many improvements:
--    1. Support for multiple modules
--    2. Currently we process everything, but we could be lazier
--       and only process what's actually needed for the particular
--       definition.
desugarNode :: [P.TopDecl] -> P.Name -> C.Node
desugarNode decls n = evalNodeDecl enumInfo theNode
  where
  ordered  = orderTopDecls decls
  noStatic = quickNoConst True ordered
  noStruct = quickNoStruct noStatic
  inlined  = quickInlineCalls noStruct
  enumInfo = getEnumInfo Nothing inlined
  theNode  = case msum (map matches inlined) of
               Just i  -> i
               Nothing -> panic "desugarNode"
                            [ "Cannot find node delcaration."
                            , "*** Name: " ++ show (pp n)
                            ]

  matches = case n of
              P.Qual {} -> panic "desugarNode"
                            [ "We only support unqualifed names for now." ]
              P.Unqual i -> \td -> case td of
                                     P.DeclareNode nd | P.nodeName nd == i ->
                                                            Just nd
                                     _                -> Nothing




