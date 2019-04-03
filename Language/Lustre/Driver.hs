-- | Process a collection of declarations all the way.
module Language.Lustre.Driver where

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List(foldl',sortBy)
import Data.Text(Text)
import AlexTools(sourceFrom,sourceIndex)
import Text.PrettyPrint(Doc)

import qualified Language.Lustre.AST as P
import qualified Language.Lustre.Core as C
import Language.Lustre.Name
import Language.Lustre.Monad
import Language.Lustre.Pretty(pp,vcatSep)
import Language.Lustre.Phase
import Language.Lustre.Transform.OrderDecls
import Language.Lustre.TypeCheck
import Language.Lustre.Transform.NoStatic
import Language.Lustre.Transform.NoStruct
import Language.Lustre.Transform.Inline
import Language.Lustre.Transform.ToCore


-- | Export a given node to core.
-- Note that currently we process all declarations, even if some
-- of them are not needed to process the given module.
quickNodeToCore ::
  Maybe Text    {- ^ Node to translate -} ->
  [P.TopDecl]   {- ^ Source decls -} ->
  LustreM (ModelInfo, C.Node)
quickNodeToCore mb ds =
  do (info,ds1) <- quickDeclsSimp ds
     nodeToCore mb info ds1

data Env = Env
  { envNodes :: Map P.OrigName ModelFunInfo
  , envEnums :: Map P.OrigName C.Expr
  }

-- | Process a bunch of declarations in preparation for translating to core.
-- This function works only on standalone declarations, not accounting
-- for a broader context.
quickDeclsSimp :: [P.TopDecl] ->
                  LustreM (Env, [P.TopDecl])
quickDeclsSimp ds =
  do ds1 <- quickOrderTopDecl ds
     let enums = getEnumInfo ds1
     dumpPhase PhaseRename $ vcatSep $ map pp ds1

     tcOn <- lustreTCEnabled
     ds2 <- if tcOn then quickCheckDecls ds1
                    else pure ds1
     dumpPhase PhaseTypecheck $ vcatSep $ map pp ds2

     (csMap,ds3) <- noConst ds2
     dumpPhase PhaseNoStatic $ vcatSep $ map pp ds3

     let nosIn = NosIn
                   { nosiStructs   = Map.empty
                   , nosiCallSites = csMap
                   }
     (nosOut,ds4) <- noStruct nosIn ds3
     dumpPhase PhaseNoStruct $ vcatSep $ map pp ds4

     (rens,ds5)   <- inlineCalls [] ds4
     dumpPhase PhaseInline $ vcatSep $ map pp ds5

     pure (Env { envNodes = mfiMap ds1 nosOut rens
               , envEnums = enums
               }
          , ds5)

dumpPhase :: LustrePhase -> Doc -> LustreM ()
dumpPhase ph doc =
  lustreIfDumpAfter ph $
     do let msg = show ph
        logMessage msg
        logMessage (replicate (length msg) '=')
        logMessage ""
        logMessage (show doc)
        logMessage ""

nodeToCore ::
  Maybe Text {- ^ Node to translate -} ->
  Env        {- ^ Info about the environment -} ->
  [P.TopDecl]                 {- ^ Simplified top decls -} ->
  LustreM (ModelInfo, C.Node)
nodeToCore mb env ds =
  do nd           <- findNode mb ds
     (varMp,core) <- evalNodeDecl (envEnums env) nd
     dumpPhase PhaseToCore (pp core)
     pure (ModelInfo { infoNodes = envNodes env
                     , infoTop   = P.identOrigName (P.nodeName nd)
                     , infoCore  = varMp
                     }
          , core)


findNode ::
  Maybe Text  {- ^ Name hint -} ->
  [P.TopDecl] {- ^ Simplified declarations -} ->
  LustreM P.NodeDecl
findNode mb ds =
  case [ nd | nd <- nodes, selected nd ] of
    [nd] -> pure nd
    [] | nd : _ <- sortBy later nodes -> pure nd
    nds  -> reportError $ BadEntryPoint
                                [ P.identOrigName (P.nodeName nd) | nd <- nds ]
  where
  nodes = [ nd | P.DeclareNode nd <- ds ]

  selected =
    case mb of
      Nothing -> hasMain
      Just t  -> \nd -> P.identText (P.nodeName nd) == t

  hasMain nd
     | Just b <- P.nodeDef nd = any isMain (P.nodeEqns b)
     | otherwise              = False


  isMain eqn = case eqn of
                 P.IsMain _ -> True
                 _          -> False

  -- XXX: assumes all declaration in the same file.
  locId = sourceIndex . sourceFrom . P.identRange . P.nodeName
  later x y = compare (locId y) (locId x)

--------------------------------------------------------------------------------
-- | Information for mapping traces back to source Lustre
data ModelInfo = ModelInfo
  { infoNodes   :: Map P.OrigName ModelFunInfo
    -- ^ Translation information for nodes.

  , infoTop     :: P.OrigName
    -- ^ Name for top node

  , infoCore    :: Map P.OrigName Ident
    -- ^ Mapping between identifiers in top-level node

  }



--------------------------------------------------------------------------------



-- | Collected information about a translated node.
-- Mostly stuff we need to map from Core models, back to original source.
data ModelFunInfo = ModelFunInfo
  { mfiCallSites :: Map CallSiteId [P.OrigName]
    {- ^ For each call site, rememebr the identifiers keeping the results
         of the call. -}

  , mfiStructs :: Map P.OrigName (StructData P.OrigName)
    {- ^ Identifiers of strucutred types (e.g., structs, arrays) are
         "exploded" into multiple variables.  This mapping remembers how
         we did that: the key is a value of a strucutred type, and
         the entry in the map is the value for it -}

  , mfiInlined :: Map [P.OrigName] (P.OrigName, Renaming)
    {- ^ Information about what we called, and how things got renamed
         when we inlined things.
         For each call site (identified by its return values),
         we have a map from the original names in the function, to the
         new names used in the inlined version. -}

  , mfiSource :: P.NodeDecl
    -- ^ The renamed, but otherwise unsimplified code for the node
    -- that implemnets this function.  See 'nodeSourceMap' for details.
  }



mfiMap :: [P.TopDecl] -> NosOut -> AllRenamings -> Map P.OrigName ModelFunInfo
mfiMap ordDs nos rens =
  Map.fromList $ map build
               $ Set.toList
               $ Set.unions [ Map.keysSet (nosoCallSites nos)
                            , Map.keysSet (nosoExpanded nos)
                            , Map.keysSet rens ]
  where
  build k = (k, ModelFunInfo { mfiCallSites = lkpMap k (nosoCallSites nos)
                             , mfiStructs   = lkpMap k (nosoExpanded nos)
                             , mfiInlined   = lkpMap k rens
                             , mfiSource    = srcMap Map.! k
                             })

  lkpMap = Map.findWithDefault Map.empty

  srcMap = nodeSourceMap ordDs



-- | Compute a mapping from node names to the actual source that implements
-- them.  For example, consider the declaration @f = g <<3>>@.  If we want to
-- see how @f@ works, we should really look for the code for @g@.
nodeSourceMap :: [P.TopDecl] -> Map P.OrigName P.NodeDecl
nodeSourceMap = foldl' add Map.empty
  where
  add mp tde =
    case tde of
      P.DeclareNode nd -> Map.insert (P.identOrigName (P.nodeName nd)) nd mp
      P.DeclareNodeInst nid ->
        case P.nodeInstDef nid of
          P.NodeInst (P.CallUser f) _
            | Just nd <- Map.lookup (P.nameOrigName f) mp ->
                         Map.insert (P.identOrigName (P.nodeInstName nid)) nd mp
          _ -> mp
      P.DeclareType {} -> mp
      P.DeclareConst {} -> mp


