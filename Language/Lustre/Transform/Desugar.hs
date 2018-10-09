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
-- node, compute the node in Core Lustre form.  If the named node does
-- not exist, a Panic exception is thrown.
--
-- XXX: This could use many improvements:
--    1. Support for multiple modules
--    2. Currently we process everything, but we could be lazier
--       and only process what's actually needed for the particular
--       definition.
desugarNode ::
  [P.TopDecl] ->
  Maybe P.Name
  {- ^ Top level function; if empty, look for one tagged with IsMain -} ->
  C.Node
desugarNode decls mbN =
  case desugarNode' decls mbN of
    Just n -> n
    Nothing -> panic "desugarNode"
               [ "Cannot find node declaration."
               , case mbN of
                   Nothing -> "*** No node has --%MAIN"
                   Just n -> "*** Name: " ++ show (pp n)
               ]

-- | Computes the node in Core Lustre form given the declaratins from
-- a single module and the name of a node; returns Nothing if the
-- named node does not exist.
desugarNode' ::
  [P.TopDecl] ->
  Maybe P.Name
  {- ^ Top level function; if empty, look for one tagged with IsMain -} ->
  Maybe C.Node
desugarNode' decls mbN = evalNodeDecl enumInfo <$> theNode
  where
  ordered  = orderTopDecls decls
  noStatic = quickNoConst True ordered
  noStruct = quickNoStruct noStatic
  inlined  = quickInlineCalls noStruct
  enumInfo = getEnumInfo Nothing inlined
  theNode  = msum (map matches inlined)

  -- if no name is specified we just pick one of the nodes that are
  -- marked with @--%MAIN@
  matches =
    case mbN of
      Nothing -> isNode checkMain
      Just nm ->
        case nm of
          P.Qual {}  -> panic "desugarNode"
                            [ "We only support unqualifed names for now." ]
          P.Unqual i -> isNode (checkByName i)

  checkMain nd = case P.nodeDef nd of
                   Just body -> any isMain (P.nodeEqns body)
                   _ -> False

  checkByName i = \nd -> P.nodeName nd == i

  isMain eqn = case eqn of
                P.IsMain -> True
                _        -> False


  isNode p = \td -> case td of
                      P.DeclareNode nd | p nd -> Just nd
                      _                       -> Nothing



