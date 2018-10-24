{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Monad where

import Data.Set(Set)
import Data.Map(Map)
import qualified Data.Map as Map
import Text.PrettyPrint
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Pretty

runTC :: M a -> Either Doc a
runTC (M m) = runM m ro0
  where
  ro0 = RO { roConstants = Map.empty
           , roUserNodes = Map.empty
           , roIdents    = Map.empty
           , roCurRange  = Nothing
           , roTypeNames = Map.empty
           , roTemporal  = False
           , roUnsafe    = False
           }


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
  { roConstants :: Map Name (SourceRange,Type)
  , roUserNodes :: Map Name (SourceRange,Safety,NodeType,NodeProfile)
  , roIdents    :: Map Ident (SourceRange, CType)
  , roCurRange  :: Maybe SourceRange
  , roTypeNames :: Map Name (SourceRange,NamedType)
  , roTemporal  :: Bool
  , roUnsafe    :: Bool
  }


data NamedType = StructTy (Map Ident Type)
               | EnumTy   (Set Ident)
               | AliasTy  Type          -- already tidied
               | AbstractTy


reportError :: Doc -> M a
reportError msg =
  M (do mb <- roCurRange <$> ask
        let msg1 = case mb of
                     Nothing -> msg
                     Just l  -> "Type error at:" <+> pp l $$ msg
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
       Just (_,t) -> pure t


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
     case Map.lookup x (roTypeNames ro) of
       Nothing -> reportError ("Undefined type:" <+> pp x)
       Just (_,nt) -> pure $ case nt of
                               AliasTy t -> t
                               _         -> NamedType x

lookupStruct :: Name -> M (Map Ident Type)
lookupStruct s =
  do ro <- M ask
     case Map.lookup s (roTypeNames ro) of
       Nothing -> reportError ("Undefined struct:" <+> pp s)
       Just (_,nt) ->
         case nt of
           StructTy fs -> pure fs
           EnumTy {}   -> reportError $ nestedError
                          "Enumeration used where a struct was expected."
                          [ "Type:" <+> pp s ]
           AliasTy at ->
             case at of
               NamedType s' -> lookupStruct s'
               _ -> reportError $ nestedError
                    "Type is not a struct."
                    [ "Type name:" <+> pp s
                    , "Type definition:" <+> pp at
                    ]

           AbstractTy -> reportError $ nestedError
                          "Abstract type used where a struct was expected."
                          ["Name:" <+> pp s]


lookupNodeProfile :: Name -> M (Safety,NodeType,NodeProfile)
lookupNodeProfile n =
  do ro <- M ask
     case Map.lookup n (roUserNodes ro) of
       Just (_,x,y,z) -> pure (x,y,z)
       Nothing -> reportError ("Undefined node:" <+> pp n)

withConst :: Ident -> Type -> M a -> M a
withConst x t (M m) =
  do ro <- M ask
     let nm = Unqual x
     let cs = roConstants ro
     M (local ro { roConstants = Map.insert nm (range x,t) cs } m)

uniqueConst :: Ident -> M ()
uniqueConst x =
  do ro <- M ask
     let nm = Unqual x
     case Map.lookup nm (roConstants ro) of
       Just (r,_) -> reportError $ nestedError
                        "Multiple definitions for constant:"
                        [ "Name:" <+> pp x
                        , "Location 1:" <+> pp r
                        , "Location 2:" <+> pp (range x)
                        ]
       Nothing -> pure ()



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

withNode :: Ident -> (Safety, NodeType, NodeProfile) -> M a -> M a
withNode x (a,b,c) (M m) =
  do ro <- M ask
     let nm = Unqual x
     case Map.lookup nm (roUserNodes ro) of
       Just (r,_,_,_) ->
         reportError $ nestedError
            "Multiple declarations for a node:"
            [ "Name:" <+> pp x
            , "Location 1:" <+> pp r
            , "Location 2:" <+> pp (range x)
            ]
       Nothing -> M (local ro { roUserNodes = Map.insert nm (range x,a,b,c)
                                                (roUserNodes ro) } m)

withNamedType :: Ident -> NamedType -> M a -> M a
withNamedType x t (M m) =
  do ro <- M ask
     let nm = Unqual x
     case Map.lookup nm (roTypeNames ro) of
       Just (r,_) -> reportError $ nestedError
                      "Multiple declaration for a type:"
                      [ "Name:" <+> pp x
                      , "Location 1" <+> pp r
                      , "Location 2" <+> pp (range x)
                      ]
       Nothing ->
        M (local ro { roTypeNames = Map.insert nm (range x,t)
                                                  (roTypeNames ro) } m)


withLocals :: [(Ident,CType)] -> M a -> M a
withLocals xs k =
  case xs of
    []           -> k
    (x,t) : more -> withLocal x t (withLocals more k)

allowTemporal :: Bool -> M a -> M a
allowTemporal b (M m) = M (mapReader upd m)
  where upd ro = ro { roTemporal = b }

checkTemporalOk :: Doc -> M ()
checkTemporalOk msg =
  do ok <- M (roTemporal <$> ask)
     unless ok $
       reportError $ nestedError
       "Temporal operators are not allowed in a function."
       [ "Operator:" <+> msg ]


allowUnsafe :: Bool -> M a -> M a
allowUnsafe b (M m) = M (mapReader upd m)
  where upd ro = ro { roUnsafe = b }

checkUnsafeOk :: Doc -> M ()
checkUnsafeOk msg =
  do ok <- M (roUnsafe <$> ask)
     unless ok $ reportError $ nestedError
       "This node does not allow calling unsafe nodes."
       [ "Unsafe call to:" <+> msg ]



