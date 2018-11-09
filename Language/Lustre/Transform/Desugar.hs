-- | Desugar a node from source-level Lustre into core-lustre
module Language.Lustre.Transform.Desugar where

import Control.Monad(msum)
import Text.PrettyPrint(hsep,punctuate,comma)
import Data.Map (Map)

import qualified Language.Lustre.AST as P
import qualified Language.Lustre.Core as C
import Language.Lustre.Pretty(pp)

import Language.Lustre.Transform.OrderDecls(orderTopDecls)
import Language.Lustre.Transform.NoStatic(quickNoConst,CallSiteId)
import Language.Lustre.Transform.NoStruct(quickNoStruct,StructData(..))
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
  (ModelInfo, C.Node)
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
  Maybe (ModelInfo, C.Node)
desugarNode' decls mbN =
  do nd <- theNode
     let (varMp,core)  = evalNodeDecl enumInfo nd
         info          = ModelInfo { infoCallSites       = simpCSInfo
                                   , infoExpandedStructs = gStructInfo
                                   , infoInlining        = allRens
                                   , infoCore            = varMp
                                   }
         cnd = case C.orderedEqns (C.nEqns core) of
                 Right es  -> core { C.nEqns = es }
                 Left recs ->
                   panic "desugarNode"
                     $ "Recursive equations in the specification:" :
                     [ "*** Binders: " ++
                         show (hsep (punctuate comma (map C.ppBinder gs)))
                         | gs <- recs
                     ]
     pure (info, cnd)
  where
  ordered  = orderTopDecls decls
  (csInfo, noStatic) = quickNoConst True ordered
  (gStructInfo,simpCSInfo,noStruct) = quickNoStruct (csInfo,noStatic)
  (allRens,inlined)  = quickInlineCalls noStruct

  enumInfo = getEnumInfo Nothing ordered
  -- XXX: noStatic already pretty much has the enumInfo
  -- so we can get it from there instead of recomputing.


  theNode =
    case mbN of
      -- Looking for a specific node
      Just nm ->
        case nm of
          P.Qual {}  -> panic "desugarNode"
                            [ "We only support unqualifed names for now." ]
          P.Unqual i -> msum (map matches inlined)
            where
            matches td =
              case td of
                P.DeclareNode nd | P.nodeName nd == i -> Just nd
                _ -> Nothing

      -- No name specified: find a node marked with --%MAIN,
      -- or use the last node
      Nothing -> do nm <- chooseDefault Nothing decls
                    case [ x | P.DeclareNode x <- inlined
                             , P.nodeName x == nm ] of
                      x : _ -> Just x
                      [] -> Nothing

  chooseDefault best xs =
    case xs of
      []     -> best
      d : ds -> case d of
                  P.DeclareNode nd
                    | checkMain nd -> Just (P.nodeName nd)
                    | otherwise    -> chooseDefault (Just (P.nodeName nd)) ds
                  _ -> chooseDefault best ds

  -- is this node marked with main
  checkMain nd = case P.nodeDef nd of
                   Just body -> any isMain (P.nodeEqns body)
                   _ -> False

    where isMain eqn = case eqn of
                         P.IsMain _ -> True
                         _          -> False

--------------------------------------------------------------------------------

data ModelInfo = ModelInfo
  { infoCallSites       :: Map P.Ident (Map CallSiteId [P.Ident])
  , infoExpandedStructs :: Map P.Ident (Map P.Ident (StructData P.Ident))
  , infoInlining        :: Map P.Ident (Map [P.Ident] (Map P.Ident P.Ident))
  , infoCore            :: Map P.Ident C.Ident
  }


