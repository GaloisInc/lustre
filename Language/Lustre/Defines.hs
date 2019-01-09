{-# Language OverloadedStrings, DataKinds, GeneralizedNewtypeDeriving #-}
module Language.Lustre.Defines
  ( getDefs
  , Defines(..)
  , Defs
  , noDefs
  , defNames
  , mergeDefs
  , ValBinder(..)
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable(traverse_)
import MonadLib

import Language.Lustre.AST


type Defs = Map Ident (Map NameSpace (Set ResolvedName))

-- | Empty set of definitinos
noDefs :: Defs
noDefs = Map.empty

-- | Merge two sets of definitions
mergeDefs :: Defs -> Defs -> Defs
mergeDefs = Map.unionWith (Map.unionWith Set.union)

-- | Collect all names in a definition map.
defNames :: Defs -> Set ResolvedName
defNames = foldr (\m xs -> foldr Set.union xs m) Set.empty




getDefs :: Defines a =>
  a               {- ^ Get definitions of this -} ->
  Maybe ModName   {- ^ Where are we -} ->
  Int             {- ^ A seed for unique names -} ->
  (Defs, Int)     {- ^ Returns definitions and a new name seed -}
getDefs a mn n0 =
  ( Map.fromListWith (Map.unionWith Set.union) (map one (defThings s))
  , defNextName s
  )
  where
  one d = (rnIdent d, Map.singleton (thingNS (rnThing d)) (Set.singleton d))
  s0    = DefS { defNextName = n0, defThings = [] }
  (_,s) = runM (unDefM (defines a)) mn s0


newtype DefM a = DefM { unDefM ::
  WithBase Id
    [ ReaderT (Maybe ModName)
    , StateT DefS
    ] a }
  deriving (Functor,Applicative,Monad)

data DefS = DefS { defNextName :: !Int
                 , defThings   :: [ResolvedName]
                 }

addDef :: Ident -> Thing -> DefM ()
addDef x t = DefM $
  do m <- ask
     sets_ $ \s ->
       let n     = defNextName s
           thing = ResolvedName { rnModule  = m
                                , rnIdent   = x
                                , rnThing   = t
                                , rnUID     = n }
       in DefS { defThings   = thing : defThings s
               , defNextName = n + 1
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

-- | A temporary to be used in situations where we know that the
-- binder introduces values (i.e., not constants)
newtype ValBinder = ValBinder Binder

instance Defines ValBinder where
  defines (ValBinder b) = addDef (binderDefines b) AVal

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



