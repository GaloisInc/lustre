{-# Language OverloadedStrings, DataKinds, GeneralizedNewtypeDeriving #-}
module Language.Lustre.Defines
  ( getDefs
  , Defines(..)
  , Defs
  , noDefs
  , defNames
  , mergeDefs
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable(traverse_)
import MonadLib

import Language.Lustre.Name
import Language.Lustre.AST
import Language.Lustre.Monad


-- | Identifiers groupes by namespace
type Defs = Map NameSpace (Set OrigName)

-- | Empty set of definitinos
noDefs :: Defs
noDefs = Map.empty

-- | Merge two sets of definitions
mergeDefs :: Defs -> Defs -> Defs
mergeDefs = Map.unionWith Set.union

-- | Collect all names in a definition map.
defNames :: Defs -> Set OrigName
defNames = Set.unions . Map.elems




getDefs :: Defines a =>
  a                 {- ^ Get definitions of this -} ->
  Maybe ModName     {- ^ Where are we -} ->
  LustreM Defs
getDefs a mn =
  do (_,defs) <- runStateT [] $ runReaderT mn $ unDefM $ defines a
     pure (Map.fromListWith Set.union (map one defs))
  where
  one i = (thingNS (rnThing i), Set.singleton i)

newtype DefM a = DefM { unDefM ::
  WithBase LustreM
    [ ReaderT (Maybe ModName)
    , StateT  [OrigName]
    ] a }
  deriving (Functor,Applicative,Monad)


addDef :: Ident -> Thing -> DefM ()
addDef x t = DefM $
  do m <- ask
     n <- inBase newInt
     sets_ $ \is -> OrigName { rnModule  = m
                             , rnThing   = t
                             , rnIdent   = x
                             , rnUID     = n } : is


class Defines t where
  defines :: t -> DefM ()


instance Defines TopDecl where
  defines ts =
    case ts of
      DeclareType td        -> defines td
      DeclareConst cd       -> defines cd
      DeclareNode nd        -> defines nd
      DeclareNodeInst nid   -> defines nid
      DeclareContract cd    -> defines cd

instance Defines ConstDef where
  defines x = addDef (constName x) AConst

instance Defines TypeDecl where
  defines td = do addDef (typeName td) AType
                  traverse_ defines (typeDef td)

instance Defines StaticParam where
  defines sp =
    case sp of
      TypeParam t       -> addDef t AType
      ConstParam c _    -> addDef c AConst
      NodeParam _ _ i _ -> addDef i ANode

instance Defines InputBinder where
  defines ib =
    case ib of
      InputBinder b  -> addDef (binderDefines b) AVal
      InputConst c _ -> addDef c AConst

-- | Note that binders are always used for values, not constants.
instance Defines Binder where
  defines b = addDef (binderDefines b) AVal

instance Defines TypeDef where
  defines td =
    case td of
      IsType _   -> pure ()
      IsEnum xs  -> sequence_ [ addDef x AConst | x <- xs ]
      IsStruct _ -> pure ()


instance Defines NodeInstDecl where
  defines nd = addDef (nodeInstName nd) ANode

instance Defines NodeDecl where
  defines nd = addDef (nodeName nd) ANode

instance Defines LocalDecl where
  defines ld =
    case ld of
      LocalVar b   -> addDef (binderDefines b) AVal
      LocalConst c -> defines c

instance Defines ContractItem where
  defines ci =
    case ci of
      GhostConst d       -> defines d
      GhostVar   b _     -> addDef (binderDefines b) AVal
      Assume _ _         -> pure ()
      Guarantee _ _      -> pure ()
      Mode _ _ _         -> pure () -- XXX: node references?
      Import _ _ _       -> pure () -- XXX: node references

instance Defines ContractDecl where
  defines c = addDef (cdName c) AContract



