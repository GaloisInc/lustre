{-# Language OverloadedStrings, GeneralizedNewtypeDeriving, DataKinds #-}
module Language.Lustre.TypeCheck.Monad where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Foldable(for_)
import Text.PrettyPrint as PP
import MonadLib

import Language.Lustre.Name
import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Monad (LustreM, LustreError(..))
import qualified Language.Lustre.Monad as L
import Language.Lustre.Panic

-- | XXX: Parameterize so that we can startin in a non-empty environment.
runTC :: M a -> LustreM a
runTC m =
  do (a,_finS) <- runStateT rw0 $ runReaderT ro0 $ unM m
     -- L.logMessage "Clock subst:"
     -- dumpClockSubstLustre (rwClockVarSubst _finS)
     pure a
  where
  ro0 = RO { roConstants  = Map.empty
           , roUserNodes  = Map.empty
           , roIdents     = Map.empty
           , roCurRange   = []
           , roTypeNames  = Map.empty
           , roTemporal   = False
           , roUnsafe     = False
           }

  rw0 = RW { rwClockVarSubst = Map.empty
           , rwClockVars = Set.empty
           }




newtype M a = M { unM ::
  WithBase LustreM
    [ ReaderT RO
    , StateT  RW
    ] a
  } deriving (Functor,Applicative,Monad)

-- | Information about a node that can be called (i.e., is in scope)
data NodeInfo = NodeInfo
  { niName         :: Ident           -- ^ Definition site
  , niSafety       :: Safety          -- ^ Safe/unsafe
  , niType         :: NodeType        -- ^ Function/node
  , niStaticParams :: [StaticParam]   -- ^ Static parametres
  , niProfile      :: NodeProfile     -- ^ Inputs and ouputs
  }

data RO = RO
  { roConstants   :: Map OrigName (SourceRange, Type)
    -- ^ Constants that are in scope. These include top-level constants,
    -- constant (i.e., static) parameters, and local constants.

  , roUserNodes   :: Map OrigName NodeInfo
    -- ^ User defined nodes in scope, as well as static node parameters.

  , roIdents      :: Map OrigName (SourceRange, CType)
    -- ^ Locals in scope (i.e., arguments and node locals)

  , roTypeNames   :: Map OrigName (SourceRange, NamedType) -- no type vars here
    -- ^ Named types in scope (top level declarations plus static parameters)

  , roCurRange    :: [SourceRange]
    -- ^ The "path" of locations that lead us to where we currently are.

  , roTemporal    :: Bool
    -- ^ Are temporal constructs OK?

  , roUnsafe      :: Bool
    -- ^ Are unsafe constucts OK?
  }


data RW = RW
  { rwClockVarSubst  :: Map CVar IClock
  , rwClockVars       :: Set CVar
    -- ^ Clock variables in the current node.
    -- Ones that don't get bound are defaulted to the base clocks.
  }

data NamedType = StructTy [FieldType]
                 -- ^ Order of the fields should match declaration
               | EnumTy   (Set OrigName)
               | AliasTy  Type
               | AbstractTy


reportError :: Doc -> M a
reportError msg =
  M $ do rs <- roCurRange <$> ask
         let msg1 = case rs of
                      [] -> msg
                      l : _  -> "Type error at:" <+> pp l $$ msg
         inBase $ L.reportError $ TCError msg1

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

lookupLocal :: Ident -> M CType
lookupLocal i =
  do ro <- M ask
     let orig = identOrigName i
     case Map.lookup orig (roIdents ro) of
       Nothing -> panic "lookupLocal"
                            [ "Undefined identifier: " ++ showPP i ]
       Just (_,t) -> pure t


lookupConst :: Name -> M Type
lookupConst c =
  do ro <- M ask
     case Map.lookup (nameOrigName c) (roConstants ro) of
       Nothing    -> panic "lookupConst" [ "Undefined constant: " ++ showPP c ]
       Just (_,t) -> pure t


resolveNamed :: Name -> M Type
resolveNamed x =
  do ro <- M ask
     case Map.lookup (nameOrigName x) (roTypeNames ro) of
       Nothing -> panic "resolveNamed" [ "Undefined type:" ++ showPP x ]
       Just (_,nt) -> pure $ case nt of
                               AliasTy t -> t
                               _         -> NamedType x

lookupStruct :: Name -> M [FieldType]
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


lookupNodeInfo :: Name -> M NodeInfo
lookupNodeInfo n =
  do ro <- M ask
     case Map.lookup (nameOrigName n) (roUserNodes ro) of
       Just info -> pure info
       Nothing -> panic "lookupNodeProfile" [ "Undefined node: " ++ showPP n ]

withConst :: Ident -> Type -> M a -> M a
withConst x t (M m) =
  do ro <- M ask
     let nm = identOrigName x
     let cs = roConstants ro
     M (local ro { roConstants = Map.insert nm (range x,t) cs } m)


withLocal :: Ident -> CType -> M a -> M a
withLocal i t (M m) =
  M $ do ro <- ask
         let is = roIdents ro
             nm = identOrigName i
         local ro { roIdents = Map.insert nm (range i, t) is } m

withNode :: NodeInfo -> M a -> M a
withNode ni (M m) =
  M $ do ro <- ask
         let nm = identOrigName (niName ni)
         local ro { roUserNodes = Map.insert nm ni (roUserNodes ro) } m

withNamedType :: Ident -> NamedType -> M a -> M a
withNamedType x t (M m) =
  M $ do ro <- ask
         let nm = identOrigName x
         local ro { roTypeNames = Map.insert nm (range x,t)
                                               (roTypeNames ro) } m


withLocals :: [(Ident,CType)] -> M a -> M a
withLocals xs k =
  case xs of
    []              -> k
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

getTemporalLevel :: M NodeType
getTemporalLevel =
  do ok <- M (roTemporal <$> ask)
     pure (if ok then Node else Function)

allowUnsafe :: Bool -> M a -> M a
allowUnsafe b (M m) = M (mapReader upd m)
  where upd ro = ro { roUnsafe = b }

getUnsafeLevel :: M Safety
getUnsafeLevel =
  do ok <- M (roUnsafe <$> ask)
     pure (if ok then Unsafe else Safe)



-- | Generate a fresh clock variable.
newClockVar :: M IClock
newClockVar = M $
  do n <- inBase L.newInt
     let cv = CVar n
     sets_ $ \rw -> rw { rwClockVars = Set.insert cv (rwClockVars rw) }
     pure (ClockVar cv)


-- | Assumes that the clock is zonked
bindClockVar :: CVar -> IClock -> M ()
bindClockVar x c =
  case c of
    ClockVar y | x == y -> pure ()
    _ -> do let upd cl = case cl of
                           ClockVar i | i == x -> c
                           _ -> cl
            M $ sets_ $ \rw -> rw { rwClockVarSubst = Map.insert x c
                                                    $ fmap upd
                                                    $ rwClockVarSubst rw
                                  , rwClockVars = Set.delete x (rwClockVars rw)
                                  }

dumpClockSubst :: M ()
dumpClockSubst = M $
  do su <- rwClockVarSubst <$> get
     lift $ lift $ dumpClockSubstLustre su

dumpClockSubstLustre :: Map CVar IClock -> LustreM ()
dumpClockSubstLustre su =
  for_ (Map.toList su) $ \(x,v) ->
    L.logMessage (show (pp x <+> ":=" <+> pp v))

debugMessage :: String -> M ()
debugMessage s = M $ lift $ lift $ L.logMessage s


-- | Generate a new scope of clock variables.  Variables that are not defined
-- by the parameter computation will be defaulted to "base clock"
inClockScope :: M a -> M a
inClockScope (M m) = M $
  do old <- sets $ \rw -> (rwClockVars rw, rw { rwClockVars = Set.empty })
     a <- m
     leftover <- rwClockVars <$> get
     let mp = Map.fromList [ (x,BaseClock) | x <- Set.toList leftover ]
     sets_ $ \rw -> rw { rwClockVars = old
                       , rwClockVarSubst = Map.union mp (rwClockVarSubst rw)
                       }
     pure a



zonkClock :: IClock -> M IClock
zonkClock c =
  case c of
    BaseClock -> pure c
    KnownClock (WhenClock r v i) ->
       do v' <- zonkExpr v
          case isId v' of
            Just j | i == j -- clocks that are always true
                    -> pure BaseClock
            _ -> pure (KnownClock (WhenClock r v' i))
    ClockVar v -> M $ do su <- rwClockVarSubst <$> get
                         pure (Map.findWithDefault c v su)
  where
  isId e = case e of
             ERange _ e1 -> isId e1
             Const e' _ -> isId e'
             Var (Unqual x) -> Just x
             _ -> Nothing



-- | Apply the substitution to types in the AST.
-- Currently, only the 'Const' construct contains a type.
zonkExpr :: Expression -> M Expression
zonkExpr expr =
  case expr of
    ERange r e -> ERange r <$> zonkExpr e
    Const e ty -> Const <$> zonkExpr e <*> zonkCType ty
    Var {}     -> pure expr
    Lit {}     -> pure expr
    e `When` c -> When <$> zonkExpr e <*> zonkClockExpr c

    Tuple es            -> Tuple <$> traverse zonkExpr es
    Array es            -> Array <$> traverse zonkExpr es
    Select e s          -> Select <$> zonkExpr e <*> zonkSelector s
    Struct s fs         -> Struct s <$> traverse zonkField fs
    UpdateStruct s e fs -> UpdateStruct s
                            <$> zonkExpr e
                            <*> traverse zonkField fs
    WithThenElse e1 e2 e3 -> WithThenElse <$> zonkExpr e1 <*>
                                              zonkExpr e2 <*> zonkExpr e3
    Merge i as -> Merge i <$> traverse zonkMergeCase as
    Call f es c -> Call f <$> traverse zonkExpr es <*> zonkClock c

zonkCType :: CType -> M CType
zonkCType ct =
  do t <- zonkType (cType ct)
     c <- zonkClock (cClock ct)
     pure CType { cType = t, cClock = c }

zonkType :: Type -> M Type
zonkType t =
  case t of
    ArrayType elT sz -> ArrayType <$> zonkType elT <*> zonkExpr sz
    IntSubrange e1 e2 -> IntSubrange <$> zonkExpr e1 <*> zonkExpr e2
    NamedType {} -> pure t
    RealType -> pure t
    IntType -> pure t
    BoolType -> pure t
    TypeRange r t' -> TypeRange r <$> zonkType t'

zonkField :: Field Expression -> M (Field Expression)
zonkField f =
  do e <- zonkExpr (fValue f)
     pure f { fValue = e }

zonkMergeCase :: MergeCase Expression -> M (MergeCase Expression)
zonkMergeCase (MergeCase k e) = MergeCase <$> zonkExpr k <*> zonkExpr e

zonkSelector :: Selector Expression -> M (Selector Expression)
zonkSelector sel =
  case sel of
    SelectField {} -> pure sel
    SelectElement e -> SelectElement <$> zonkExpr e
    SelectSlice e   -> SelectSlice <$> zonkSlice e

zonkSlice :: ArraySlice Expression -> M (ArraySlice Expression)
zonkSlice a =
  do s <- zonkExpr (arrayStart a)
     e <- zonkExpr (arrayEnd a)
     t <- traverse zonkExpr (arrayStep a)
     pure ArraySlice { arrayStart = s, arrayEnd = e, arrayStep = t }

zonkClockExpr :: ClockExpr -> M ClockExpr
zonkClockExpr (WhenClock r e i) =
  do e' <- zonkExpr e
     pure (WhenClock r e' i)

zonkBody :: NodeBody -> M NodeBody
zonkBody b =
  do eqs <- traverse zonkEqn (nodeEqns b)
     pure b { nodeEqns = eqs }

zonkEqn :: Equation -> M Equation
zonkEqn eqn =
  case eqn of
    Assert p e -> Assert p <$> zonkExpr e
    Property p e -> Property p <$> zonkExpr e
    IsMain {} -> pure eqn
    IVC {} -> pure eqn
    Realizable {} -> pure eqn
    Define lhs e -> Define lhs <$> zonkExpr e

zonkContract :: Contract -> M Contract
zonkContract c =
  do cis <- mapM zonkContractItem (contractItems c)
     pure c { contractItems = cis }

zonkContractItem :: ContractItem -> M ContractItem
zonkContractItem ci =
  case ci of
    Assume e    -> Assume    <$> zonkExpr e
    Guarantee e -> Guarantee <$> zonkExpr e
    _ -> panic "zonkContractItem" ["unsupported contract item"]

