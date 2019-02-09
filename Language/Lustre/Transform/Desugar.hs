-- | Desugar a node from source-level Lustre into core-lustre
module Language.Lustre.Transform.Desugar where

import Control.Monad(msum)
import Text.PrettyPrint(hsep,punctuate,comma)
import Data.List(foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set


import qualified Language.Lustre.AST as P
import qualified Language.Lustre.Core as C
import Language.Lustre.Pretty(pp)

import Language.Lustre.Transform.OrderDecls(orderTopDecls)
import Language.Lustre.Transform.NoStatic(quickNoConst,CallSiteId)
import Language.Lustre.Transform.NoStruct
import Language.Lustre.Transform.Inline
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

reportDepError :: ResolveError -> a
reportDepError = error . show

-- | Computes the node in Core Lustre form given the declaratins from
-- a single module and the name of a node; returns Nothing if the
-- named node does not exist.
desugarNode' ::
  [P.TopDecl] ->
  Maybe P.Name
  {- ^ Top level function; if empty, look for one tagged with IsMain -} ->
  Maybe (ModelInfo, C.Node)
desugarNode' decls mbN =
  do ordered            <- orderTopDecls decls
     (csInfo, noStatic) <- noConst ordered
     undefined

  do nd <- theNode
     let (varMp,core)  = evalNodeDecl enumInfo nd
         info = ModelInfo
                  { infoNodes = mfiMap simpCSInfo gStructInfo allRens
                  , infoCore  = varMp
                  , infoSource = nodeSourceMap ordered
                  , infoTop = P.nodeName nd
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

-- | Information for mapping traces back to source Lustre
data ModelInfo = ModelInfo
  { infoNodes   :: Map P.Ident ModelFunInfo
    -- ^ Translation information for nodes.

  , infoSource  :: Map P.Ident P.NodeDecl
    -- ^ Source for each node

  , infoCore    :: Map P.Ident C.Ident
    -- ^ Mapping between identifiers in top-level node

  , infoTop     :: P.Ident
    -- ^ Name for top module
  }

mfiMap ::
  Map P.Ident (Map CallSiteId [P.Ident]) ->
  Map P.Ident (Map P.Ident (StructData P.Ident)) ->
  Map P.Ident (Map [P.Ident] (P.Name, Map P.Ident P.Ident)) ->
  Map P.Ident ModelFunInfo
mfiMap csi sdi ii = Map.fromList
                  $ map build
                  $ Set.toList
                  $ Set.unions
                    [ Map.keysSet csi
                    , Map.keysSet sdi
                    , Map.keysSet ii ]
  where
  build k = (k, ModelFunInfo { mfiCallSites = lkpMap k csi
                             , mfiStructs   = lkpMap k sdi
                             , mfiInlined   = lkpMap k ii
                             })



-- | Look up a map, returning an empty one, if no entry.
lkpMap :: Ord a => a -> Map a (Map b c) -> Map b c
lkpMap = Map.findWithDefault Map.empty

-- | Collected information about a translated node.
-- Mostly stuff we need to map from Core models, back to original source.
data ModelFunInfo = ModelFunInfo
  { mfiCallSites :: Map CallSiteId [P.Ident]
    {- ^ Identifies call sites, and keeps the identifiers containg the
        results of the call -}
  , mfiStructs :: Map P.Ident (StructData P.Ident)
    {- ^ Identifiers of strucutred types (e.g., structs, arrays) are
         "exploded" into multiple variables.  This mapping remembers how
         we did that: the key is an identify of a strucutred type, and
         the entry in the map is the value for it -}
  , mfiInlined :: Map [P.Ident] (P.Name, Map P.Ident P.Ident)
    {- ^ Information about what we called, and how things got renamed
         when we inlined things.
         For each call site (identified by its return values),
         we have a map from the original names in the function, to the
         new names used in the inlined version. -}
  }


--------------------------------------------------------------------------------

-- | Compute a mapping from node names, to the actual source that implements
-- them.  This is an issue as Lustre supports things like: @f = g<<3>>@,
-- which means that @f@ is the node @g@ with a specific static argument.
-- So the code for @f@ is really @g@ (or, rather, whatever implmentes @g@).
-- XXX: Does not support qualified names for now.
nodeSourceMap :: [P.TopDecl] -> Map P.Ident P.NodeDecl
nodeSourceMap = foldl' add Map.empty
  where
  add mp tde =
    case tde of
      P.DeclareNode nd -> Map.insert (P.nodeName nd) nd mp
      P.DeclareNodeInst nid ->
        case P.nodeInstDef nid of
          P.NodeInst (P.CallUser (P.Unqual x)) _
            | Just nd <- Map.lookup x mp ->
                          Map.insert (P.nodeInstName nid) nd mp
          _ -> mp
      P.DeclareType {} -> mp
      P.DeclareConst {} -> mp


