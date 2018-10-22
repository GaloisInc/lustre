{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Monad where

import Data.Map(Map)
import qualified Data.Map as Map
import Text.PrettyPrint
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Pretty


-- | A single clock expression.
data IClock     = BaseClock
                | KnownClock ClockExpr
                | ConstExpr -- ^ Any clock we want

instance Pretty IClock where
  ppPrec n c = case c of
                 BaseClock    -> "base clock"
                 KnownClock k -> ppPrec n k
                 ConstExpr    -> "an arbitrary clock"

-- | A type, together with its clock.
data CType      = CType { cType :: Type, cClock :: IClock }




newtype M a = M { unM :: ReaderT RO (ExceptionT Doc Id) a }

instance Functor M where
  fmap f (M m) = M (fmap f m)

instance Applicative M where
  pure a        = M (pure a)
  M mf <*> M ma = M (mf <*> ma)

instance Monad M where
  M ma >>= k    = M (ma >>= unM . k)



data RO = RO
  { roConstants :: Map Name Type
  , roUserNodes :: Map Name NodeProfile
  , roIdents    :: Map Ident (SourceRange, CType)
  , roCurRange  :: Maybe SourceRange
  , roStructs   :: Map Name (Map Ident Type)
  , roTypeAlias :: Map Name Type
  }

reportError :: Doc -> M a
reportError msg =
  M (do mb <- roCurRange <$> ask
        let msg1 = case mb of
                     Nothing -> msg
                     Just l  -> "Error at:" <+> pp l $$ msg
        raise msg1)

notYetImplemented :: Doc -> M a
notYetImplemented f =
  reportError $ nestedError "XXX: Feature not yet implemented:"
                            [ "Feature:" <+> f ]

nestedError :: Doc -> [Doc] -> Doc
nestedError x ys = vcat (x : [ "***" <+> y | y <- ys ])

inRange :: SourceRange -> M a -> M a
inRange r (M a) = M (mapReader upd a)
  where upd ro = ro { roCurRange = Just r }

lookupIdentMaybe :: Ident -> M (Maybe CType)
lookupIdentMaybe i = M (fmap snd . Map.lookup i . roIdents <$> ask)

lookupIdent :: Ident -> M CType
lookupIdent i =
  do mb <- lookupIdentMaybe i
     case mb of
       Just t  -> pure t
       Nothing -> reportError ("Undefined identifier:" <+> pp i)

lookupConst :: Name -> M Type
lookupConst c =
  do ro <- M ask
     case Map.lookup c (roConstants ro) of
       Nothing -> reportError ("Undefined constant:" <+> pp c)
       Just t  -> pure t

-- | Remove outermost 'TypeRange' and type-aliases.
tidyType :: Type -> M Type
tidyType t =
  case t of
    TypeRange _ t1 -> tidyType t1
    NamedType x    -> resolveNamed x
    _              -> pure t

resolveNamed :: Name -> M Type
resolveNamed x =
  do ro <- M ask
     pure (Map.findWithDefault (NamedType x) x (roTypeAlias ro))

lookupStruct :: Name -> M (Map Ident Type)
lookupStruct s =
  do ro <- M ask
     case Map.lookup s (roStructs ro) of
       Just fs -> pure fs
       Nothing -> reportError ("Undefined struct:" <+> pp s)

lookupNodeProfile :: Name -> M NodeProfile
lookupNodeProfile n =
  do ro <- M ask
     case Map.lookup n (roUserNodes ro) of
       Just t  -> pure t
       Nothing -> reportError ("Undefined node:" <+> pp n)

withLocal :: Ident -> CType -> M a -> M a
withLocal i t (M m) =
  do ro <- M ask
     let is = roIdents ro
     case Map.lookup i is of
       Nothing -> M (local ro { roIdents = Map.insert i (range i, t) is } m)
       Just (r,_) ->
         reportError $ nestedError
           "Multiple declarations for a local variable:"
           [ "Name:" <+> pp i
           , "Location 1:" <+> pp r
           , "Location 2:" <+> pp (range i)
           ]

withLocals :: [(Ident,CType)] -> M a -> M a
withLocals xs k =
  case xs of
    []           -> k
    (x,t) : more -> withLocal x t (withLocals more k)

