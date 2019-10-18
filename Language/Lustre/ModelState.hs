module Language.Lustre.ModelState
  ( -- * Locations and Navigation
    Loc, locTop, ModelInfo, locCalls, enterCall, exitCall, locName,

    -- * Call sites
    CallSiteId, callSiteName,

    -- * Accessing Variables
    S, Vars(..), lookupVars, locVars,
    -- * Names
    CoreValue, SourceValue,
  ) where

import Data.Map (Map)
import qualified Data.Map as Map

import Language.Lustre.Name
import qualified Language.Lustre.AST  as P
import Language.Lustre.Core(CoreName,coreNameFromOrig)
import Language.Lustre.Transform.NoStatic(CallSiteId,callSiteName)
import Language.Lustre.Transform.NoStruct(StructData(..))
import Language.Lustre.Transform.Inline(Renaming(..))
import Language.Lustre.Transform.ToCore(enumFromVal)
import Language.Lustre.Driver(ModelInfo(..), ModelFunInfo(..))
import qualified Language.Lustre.Semantics.Core as L
import qualified Language.Lustre.Semantics.Value as V
import Language.Lustre.Panic(panic)

-- | A state for a core lustre program.
type S            = Map CoreName CoreValue
type CoreValue    = L.Value -- ^ Value for a core expression
type SourceValue  = V.Value -- ^ Value for full Lustre

--------------------------------------------------------------------------------

-- | A 'Loc' is an instantiation of a function with specific arguments.
-- It helps is traverse the call tree at a specific state in the system.
data Loc = Loc
  { lModel     :: ModelInfo
    {- ^ Read only. For convenience we pass around the whole model info,
    so that we can access global thing (e.g., the lustre to core variable
    mapping) -}

  , lFunInfo   :: ModelFunInfo
    {- ^ Information about the translation of the specific function we are in -}

  , lSubst     :: Map OrigName OrigName
    {- ^ Accumulated renamings for variables resulting from Lustre-Lustre
         translations -}

  , lVars      :: Vars (OrigName, P.Type)
    -- ^ These are the variables we are observing.

  , lAbove     :: Maybe Loc
    -- ^ Locations on the current call path.  This is for navigation,
    -- so we can go back to our parent.

  , lRange     :: P.SourceRange
    -- ^ Location in the source code for this node
  }

-- | Get the name of node corresponding to the current location.
locName :: Loc -> OrigName
locName = identOrigName . P.nodeName . mfiSource . lFunInfo

instance P.HasRange Loc where
  range = lRange

-- | The location corresponding to the main function being verified.
locTop :: ModelInfo -> Maybe Loc
locTop mi =
  do let top = infoTop mi
     fi <- Map.lookup top (infoNodes mi)
     let nd = mfiSource fi
     pure Loc { lModel = mi
              , lFunInfo = fi
              , lSubst = Map.empty
              , lVars = nodeVars nd
              , lAbove = Nothing
              , lRange = P.range nd
              }

-- | Given a location and a call site in it, get the location corresponding
-- to the given call.
enterCall :: Loc -> CallSiteId -> Maybe Loc
enterCall l cs =
  do let mf = lFunInfo l
     xs     <- Map.lookup cs (mfiCallSites mf)
     (f,ren) <- Map.lookup xs (mfiInlined mf)
     let su = renVarMap ren
     let mi = lModel l
     fi <- Map.lookup f (infoNodes mi)
     let nd = mfiSource fi
     let vars = nodeVars nd
         su1  = fmap (\i -> Map.findWithDefault i i (lSubst l)) su
     pure l { lFunInfo = fi
            , lSubst = su1
            , lVars = vars
            , lAbove = Just l
            , lRange = P.range nd
            }

-- | What are the callsites avaialable at a location.
locCalls :: Loc -> [CallSiteId]
locCalls = Map.keys . mfiCallSites . lFunInfo

-- | Got back to the parent of a location.
exitCall :: Loc -> Maybe Loc
exitCall = lAbove


--------------------------------------------------------------------------------

-- | The variables at this location.
locVars :: Loc -> Vars (OrigName, P.Type)
locVars = lVars

-- | Get the values for all varialbes in a location.
lookupVars :: Loc -> S -> Vars (OrigName, P.Type, Maybe SourceValue)
lookupVars l s = fmap lkp (lVars l)
  where lkp (i,t) = (i, t, lookupVar l s t i)


-- | Get the value for a variable in a location, in a specific state.
lookupVar :: Loc -> S -> P.Type -> OrigName -> Maybe SourceValue
lookupVar l s t i0 =
  case Map.lookup i (mfiStructs (lFunInfo l)) of
    Just si ->
      do si1 <- traverse (lookupVar l s t) si
         pure (restruct si1)
    Nothing ->
      do v1 <- Map.lookup (coreNameFromOrig i) s
         reval l t v1
  where
  i = Map.findWithDefault i0 i0 (lSubst l)


-- | Change representations of values.
reval :: Loc -> P.Type -> L.Value -> Maybe SourceValue
reval loc t val =
  case val of
    L.VInt n
      | P.NamedType tn <- t
      , let tno = nameOrigName tn
      , Just c <- Map.lookup (tno,n) (enumFromVal (infoEnums (lModel loc)))
                   -> Just (V.VEnum tno c)
      | otherwise  -> Just (V.VInt n)
    L.VBool n -> Just (V.VBool n)
    L.VReal n -> Just (V.VReal n)
    L.VNil    -> Nothing


-- | Change of representations.
restruct :: StructData SourceValue -> SourceValue
restruct str =
  case str of
    SLeaf a       -> a
    SArray xs     -> V.VArray (map restruct xs)
    SStruct x vs  -> V.VStruct x (fmap (fmap restruct) vs)
    STuple {}     -> panic "restruct" ["Unexpected tuple"]



--------------------------------------------------------------------------------
-- | This is what we report
data Vars i = Vars
  { vIns  :: [i]
  , vLocs :: [i]
  , vOuts :: [i]
  } deriving Show

instance Functor Vars where
  fmap f vs = Vars { vIns   = fmap f (vIns vs)
                   , vLocs  = fmap f (vLocs vs)
                   , vOuts  = fmap f (vOuts vs)
                   }

instance Foldable Vars where
  foldMap f vs = mconcat [ foldMap f (vIns vs)
                         , foldMap f (vLocs vs)
                         , foldMap f (vOuts vs)
                         ]

instance Traversable Vars where
  traverse f vs = Vars <$> traverse f (vIns vs)
                       <*> traverse f (vLocs vs)
                       <*> traverse f (vOuts vs)


-- | Get the variables from a node.
nodeVars :: P.NodeDecl -> Vars (OrigName, P.Type)
nodeVars nd = Vars { vIns = fromB [ b | P.InputBinder b <- P.nodeInputs prof ]
                   , vLocs = fromB locs
                   , vOuts = fromB (P.nodeOutputs prof)
                   }
  where
  prof = P.nodeProfile nd
  locs = case P.nodeDef nd of
           Nothing -> []
           Just d -> [ b | P.LocalVar b <- P.nodeLocals d ]
  fromB bs = [ ( identOrigName (P.binderDefines b)
               , P.cType (P.binderType b)
               )
             | b <- bs ]

