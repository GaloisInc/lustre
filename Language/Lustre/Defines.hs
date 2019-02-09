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

import Language.Lustre.AST
import Language.Lustre.Monad(NameSeed,nameSeedToInt,nextNameSeed)


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
  NameSeed          {- ^ A seed for unique names -} ->
  (Defs, NameSeed)  {- ^ Returns definitions and a new name seed -}
getDefs a mn n0 =
  ( Map.fromListWith Set.union (map one (defThings s))
  , defNextName s
  )
  where
  one i = (thingNS (rnThing i), Set.singleton i)
  s0    = DefS { defNextName = n0, defThings = [] }
  (_,s) = runM (unDefM (defines a)) mn s0


newtype DefM a = DefM { unDefM ::
  WithBase Id
    [ ReaderT (Maybe ModName)
    , StateT DefS
    ] a }
  deriving (Functor,Applicative,Monad)

data DefS = DefS { defNextName :: !NameSeed
                 , defThings   :: [OrigName]
                 }

addDef :: Ident -> Thing -> DefM ()
addDef x t = DefM $
  do m <- ask
     sets_ $ \s ->
       let n    = defNextName s
           info = OrigName { rnModule  = m
                          , rnThing   = t
                          , rnIdent   = x
                          , rnUID     = nameSeedToInt n }
       in DefS { defThings   = info : defThings s
               , defNextName = nextNameSeed n
               }


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
      GhostConst x _ _   -> addDef x AConst
      GhostVar   b _     -> addDef (binderDefines b) AVal
      Assume _           -> pure ()
      Guarantee _        -> pure ()
      Mode _ _ _         -> pure () -- XXX: node references?
      Import _ _ _       -> pure () -- XXX: node references

instance Defines ContractDecl where
  defines c = addDef (cdName c) AContract



