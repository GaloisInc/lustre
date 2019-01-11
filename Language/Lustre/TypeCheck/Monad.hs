{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Monad where

import Data.Set(Set)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe(listToMaybe)
import Text.PrettyPrint as PP
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic

runTC :: M a -> Either Doc a
runTC (M m) = case runM m ro0 rw0 of
                Left err -> Left err
                Right (a,_) -> Right a
  where
  ro0 = RO { roConstants  = Map.empty
           , roUserNodes  = Map.empty
           , roIdents     = Map.empty
           , roOnlyInputs = False
           , roCurRange   = []
           , roTypeNames  = Map.empty
           , roTemporal   = False
           , roUnsafe     = False
           }

  rw0 = RW { rwNextClockVar = 0
           , rwClockVarSubst = Map.empty
           , rwNextTVar = 0
           , rwTyVarSubst = Map.empty
           , rwCtrs = []
           }

data Constraint = Subtype Type Type
                | Arith1 Doc Type Type      -- op ^ in, out
                | Arith2 Doc Type Type Type -- ^ op, in1, in2, out
                | CmpEq Doc Type Type       -- ^ op in1, in2
                | CmpOrd Doc Type Type      -- ^ op, in1, in2

-- | A single clock expression.
data IClock     = BaseClock
                | KnownClock ClockExpr
                | ClockVar CVar

-- | A clock variable
newtype CVar    = CVar Int deriving (Eq,Ord)

instance Pretty IClock where
  ppPrec n c = case c of
                 BaseClock    -> "base clock"
                 KnownClock k -> ppPrec n k
                 ClockVar v   -> pp v

instance Pretty CVar where
  ppPrec _ (CVar i) = "cv_" PP.<> pp i


-- | A type, together with its clock.
data CType      = CType { cType :: Type, cClock :: IClock }




newtype M a = M { unM :: ReaderT RO
                        (StateT  RW
                        (ExceptionT Doc
                         Id)) a }

instance Functor M where
  fmap f (M m) = M (fmap f m)

instance Applicative M where
  pure a        = M (pure a)
  M mf <*> M ma = M (mf <*> ma)

instance Monad M where
  M ma >>= k    = M (ma >>= unM . k)



data RO = RO
  { roConstants   :: Map OrigName (SourceRange, Type)
  , roUserNodes   :: Map OrigName (SourceRange, Safety,NodeType,NodeProfile)
  , roIdents      :: Map OrigName (SourceRange, IdentMode, CType)
  , roTypeNames   :: Map OrigName (SourceRange, NamedType) -- no type vars here
  , roOnlyInputs  :: Bool
  , roCurRange    :: [SourceRange]
  , roTemporal    :: Bool
  , roUnsafe      :: Bool
  }

data IdentMode = InputIdent | NonInputIdent

data RW = RW
  { rwNextClockVar   :: !Int
  , rwClockVarSubst  :: Map CVar IClock
  , rwNextTVar       :: !Int
  , rwTyVarSubst     :: Map TVar Type   -- ^ tv equals
  , rwCtrs           :: [(Maybe SourceRange, Constraint)]
                        -- ^ delayed constraints
  }

data NamedType = StructTy (Map Ident Type)  -- ^ The Ident's are just labels
               | EnumTy   (Set OrigName)
               | AliasTy  Type              -- ^ already tidied
               | AbstractTy


reportError :: Doc -> M a
reportError msg =
  M (do rs <- roCurRange <$> ask
        let msg1 = case rs of
                     [] -> msg
                     l : _  -> "Type error at:" <+> pp l $$ msg
        raise msg1)

notYetImplemented :: Doc -> M a
notYetImplemented f =
  reportError $ nestedError "XXX: Feature not yet implemented:"
                            [ "Feature:" <+> f ]

nestedError :: Doc -> [Doc] -> Doc
nestedError x ys = vcat (x : [ "***" <+> y | y <- ys ])

inRange :: SourceRange -> M a -> M a
inRange r (M a) = M (mapReader upd a)
  where upd ro = ro { roCurRange = r : roCurRange ro }

inRangeSet :: SourceRange -> M a -> M a
inRangeSet r (M a) = M (mapReader upd a)
  where upd ro = ro { roCurRange = [r] }

inRangeSetMaybe :: Maybe SourceRange -> M a -> M a
inRangeSetMaybe mb m = case mb of
                         Nothing -> m
                         Just r -> inRangeSet r m

inRangeMaybe :: Maybe SourceRange -> M a -> M a
inRangeMaybe mb m = case mb of
                      Nothing -> m
                      Just r  -> inRange r m

onlyInputs :: M a -> M a
onlyInputs (M m) = M (mapReader (\ro -> ro { roOnlyInputs = True }) m)

lookupLocal :: Ident -> M CType
lookupLocal i =
  do ro <- M ask
     let orig = identOrigName i
     case Map.lookup orig (roIdents ro) of
       Nothing -> panic "lookupLocal"
                            [ "Undefined identifier: " ++ showPP i ]
       Just (_,mo,t) ->
         case mo of
           NonInputIdent | roOnlyInputs ro ->
             reportError $ "Local variable" <+> backticks (pp i) <+>
                           "is not an input."
           _ -> pure t


lookupConst :: Name -> M Type
lookupConst c =
  do ro <- M ask
     case Map.lookup (nameOrigName c) (roConstants ro) of
       Nothing    -> panic "lookupConst" [ "Undefined constant: " ++ showPP c ]
       Just (_,t) -> pure t


-- | Remove outermost 'TypeRange', type-aliases, lookup binding for type vars.
tidyType :: Type -> M Type
tidyType t =
  case t of
    TypeRange _ t1 -> tidyType t1
    NamedType x    -> resolveNamed x
    TVar x         -> resolveTVar x
    _              -> pure t

tidyConstraint :: Constraint -> M Constraint
tidyConstraint ctr =
  case ctr of
    Subtype a b     -> Subtype  <$> tidyType a <*> tidyType b
    Arith1 x a b    -> Arith1 x <$> tidyType a <*> tidyType b
    Arith2 x a b c  -> Arith2 x <$> tidyType a <*> tidyType b <*> tidyType c
    CmpEq x a b     -> CmpEq x  <$> tidyType a <*> tidyType b
    CmpOrd x a b    -> CmpOrd x <$> tidyType a <*> tidyType b

resolveNamed :: Name -> M Type
resolveNamed x =
  do ro <- M ask
     case Map.lookup (nameOrigName x) (roTypeNames ro) of
       Nothing -> panic "resolveNamed" [ "Undefined type:" ++ showPP x ]
       Just (_,nt) -> pure $ case nt of
                               AliasTy t -> t
                               _         -> NamedType x

resolveTVar :: TVar -> M Type
resolveTVar tv =
  do su <- M (rwTyVarSubst <$> get)
     pure (Map.findWithDefault (TVar tv) tv su)

lookupStruct :: Name -> M (Map Ident Type)
lookupStruct s =
  do ro <- M ask
     case Map.lookup (nameOrigName s) (roTypeNames ro) of
       Nothing -> panic "lookupStruct" [ "Undefined struct: " ++ showPP s ]
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
     case Map.lookup (nameOrigName n) (roUserNodes ro) of
       Just (_,x,y,z) -> pure (x,y,z)
       Nothing -> panic "lookupNodeProfile" [ "Undefined node: " ++ showPP n ]

withConst :: Ident -> Type -> M a -> M a
withConst x t (M m) =
  do ro <- M ask
     let nm = identOrigName x
     let cs = roConstants ro
     M (local ro { roConstants = Map.insert nm (range x,t) cs } m)


withLocal :: Ident -> IdentMode -> CType -> M a -> M a
withLocal i mo t (M m) =
  M $ do ro <- ask
         let is = roIdents ro
             nm = identOrigName i
         local ro { roIdents = Map.insert nm (range i, mo, t) is } m

withNode :: Ident -> (Safety, NodeType, NodeProfile) -> M a -> M a
withNode x (a,b,c) (M m) =
  M $ do ro <- ask
         let nm = identOrigName x
         local ro { roUserNodes = Map.insert nm (range x,a,b,c)
                                                (roUserNodes ro) } m

withNamedType :: Ident -> NamedType -> M a -> M a
withNamedType x t (M m) =
  M $ do ro <- ask
         let nm = identOrigName x
         local ro { roTypeNames = Map.insert nm (range x,t)
                                               (roTypeNames ro) } m


withLocals :: [(Ident,IdentMode,CType)] -> M a -> M a
withLocals xs k =
  case xs of
    []              -> k
    (x,mo,t) : more -> withLocal x mo t (withLocals more k)

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

newClockVar :: M IClock
newClockVar = M $ do n <- sets $ \rw -> let next = rwNextClockVar rw
                                        in (next, rw { rwNextClockVar = next+1})
                     pure (ClockVar (CVar n))


-- | Assumes that the clock is zonked
bindClockVar :: CVar -> IClock -> M ()
bindClockVar x c =
  case c of
    ClockVar y | x == y -> pure ()
    _ -> M $ sets_ $ \rw -> rw { rwClockVarSubst = Map.insert x c
                                                 $ rwClockVarSubst rw }



zonkClock :: IClock -> M IClock
zonkClock c =
  case c of
    BaseClock -> pure c
    KnownClock {} -> pure c
    ClockVar v -> M $ do su <- rwClockVarSubst <$> get
                         pure (Map.findWithDefault c v su)


newTVar :: M Type
newTVar = M $ do n <- sets $ \rw -> let next = rwNextTVar rw
                                    in (next, rw { rwNextTVar = next+1 })
                 pure (TVar (TV n))

-- | Assumes that the type is tidied.  Note that tidying is shallow,
-- so we need to keep tidying in the occurs check
bindTVar :: TVar -> Type -> M ()
bindTVar x t =
  case t of
    TVar y | x == y -> pure ()
    _ -> do occursCheck t
            M $ sets_ $ \rw ->
                         rw { rwTyVarSubst = Map.insert x t (rwTyVarSubst rw) }

  where
  occursCheck ty =
    do t1 <- tidyType ty
       case t1 of
         TVar y | x == y -> reportError $ nestedError
                            "Recursive type"
                            [ "Variable:" <+> pp x
                            , "Occurs in:" <+> pp t ]
         ArrayType elT _ -> occursCheck elT
         _ -> pure ()

addConstraint :: Constraint -> M ()
addConstraint c =
  do r <- listToMaybe . roCurRange <$> M ask
     M $ sets_ $ \rw -> rw { rwCtrs = (r, c) : rwCtrs rw }


resetConstraints :: M [(Maybe SourceRange, Constraint)]
resetConstraints = M $ sets $ \rw -> (rwCtrs rw, rw { rwCtrs = [] })

