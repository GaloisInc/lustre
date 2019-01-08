{-# Language DataKinds, GeneralizedNewtypeDeriving, TypeFamilies #-}
module Language.Lustre.Transform.OrderDecls (orderTopDecls) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup ( (<>) )
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe(mapMaybe)
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import Data.Foldable(traverse_)
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Pretty(showPP)
import Language.Lustre.Panic(panic)
import Language.Lustre.Defines


orderTopDecls :: [TopDecl] -> [TopDecl]
orderTopDecls = concatMap orderRec . orderThings

-- XXX
-- | Place declarations with no static parameters after declarations with
-- static parameters.  We assume that the inputs were already validated,
-- so this does not do proper error checking.
orderRec :: SCC TopDecl -> [TopDecl]
orderRec comp =
  case comp of
    AcyclicSCC x -> [x]
    CyclicSCC xs -> case break noParam xs of
                      (as,b:bs) -> as ++ bs ++ [b]
                      _         -> xs
      where
      noParam td =
        case td of
          DeclareNode nd      -> null (nodeStaticInputs nd)
          DeclareNodeInst nid -> null (nodeInstStaticInputs nid)
          _                   -> False

orderThings :: (Defines a, Resolve a) => [a] -> [SCC a]
orderThings ds = undefined {-stronglyConnComp graph
  where
  getRep x = Map.findWithDefault x x repMap

  (repMap, graph) = foldr addRep (Map.empty,[]) ds

  addRep d (mp, gs) = undefined {
    case Set.minView (getDefs d) of
      Nothing -> (mp,gs)    -- shouldn't happen?
      Just (a,rest) ->
        ( foldr (\x -> Map.insert x a) mp rest
        , (d, a, map getRep (Set.toList (resolve d))) : gs
        ) -}


{- | Order an unordered set of declarations, in dependency order.
The result is a dependency-ordered sequence of strongly-connected
components, and the new names introduced by the declarations -}
resolveGroup :: (Defines a, Resolve a) => [a] -> ResolveM ([SCC a], InScope)
resolveGroup ds =
  do (namess, newScope) <- defsOf ds
     resolved <- extendScope newScope (traverse resolveWithFree ds)
     let mkRep i ns = [ (n,i) | n <- Set.toList ns ]
         repFor     = (`Map.lookup` mp)
            where mp = Map.fromList $ concat $ zipWith mkRep [ 0 .. ] namess
         mkNode i (a,us) = (a, i, mapMaybe repFor (Set.toList us))
         comps = stronglyConnComp (zipWith mkNode [0..] resolved)
         localDef = Set.unions namess
         allUsed  = Set.unions (map snd resolved) `Set.difference` localDef
     traverse_ addUse allUsed
     pure (comps, newScope)

-- | Check that none of the given SCC-s are recursive.
noRec :: (a -> Ident) {- ^ Pick an identifier to use for the given entry.
                           This is used for error reporting. -} ->
          [SCC a] ->
          ResolveM [a]
noRec nm = traverse check
  where check x = case x of
                    AcyclicSCC a -> pure a
                    CyclicSCC as -> reportError (BadRecursiveDefs (map nm as))

-- | Resolve an unordered group of declarations,
-- checking that none are recursive.
resolveNonRecGroup ::
  (Defines a, Resolve a) =>
  (a -> Ident) {- ^ Use this name when reporting errors -} ->
  [a]          {- ^ Unordered declarations -} ->
  ResolveM ([a], InScope)
resolveNonRecGroup isRec xs =
  do (comps,scope) <- resolveGroup xs
     xs <- noRec isRec comps
     pure (xs, scope)




--------------------------------------------------------------------------------

class Resolve t where
  resolve :: t -> ResolveM t


instance Resolve TopDecl where
  resolve ts =
    case ts of
      DeclareType td      -> DeclareType     <$> resolve td
      DeclareConst cd     -> DeclareConst    <$> resolve cd
      DeclareNode nd      -> DeclareNode     <$> resolve nd
      DeclareNodeInst nid -> DeclareNodeInst <$> resolve nid
      DeclareContract cd  -> DeclareContract <$> resolve cd

instance Resolve TypeDecl where
  resolve t = do t1 <- traverse resolve (typeDef t)
                 pure t { typeDef = t1 }

instance Resolve TypeDef where
  resolve td =
    case td of
      IsType t    -> IsType <$> resolve t
      IsEnum _    -> pure td
      IsStruct fs -> IsStruct <$> traverse resolve fs

instance Resolve FieldType where
  resolve ft = do t1 <- resolve (fieldType ft)
                  e1 <- traverse resolveConstExpr (fieldDefault ft)
                  pure ft { fieldType = t1, fieldDefault = e1 }

resolveField :: (e -> ResolveM e) -> Field e -> ResolveM (Field e)
resolveField res (Field l e) = Field l <$> res e

instance Resolve Type where
  resolve ty =
    case ty of
      TypeRange r t     -> TypeRange r  <$> resolve t

      NamedType t       -> NamedType    <$> resolveName t AType
      ArrayType t e     -> ArrayType    <$> resolve t <*> resolveConstExpr e
      IntSubrange e1 e2 -> IntSubrange  <$> resolveConstExpr e1
                                        <*> resolveConstExpr e2

      IntType           -> pure ty
      RealType          -> pure ty
      BoolType          -> pure ty

      TVar x            -> panic "resolve@Type" [ "Unexpected type variable"
                                             , "*** Tvar: " ++ showPP x ]

instance Resolve ConstDef where
  resolve cd = do t <- traverse resolve (constType cd)
                  e <- traverse resolveConstExpr (constDef cd)
                  pure cd { constType = t, constDef = e }


instance Resolve StaticParam where
  resolve sp =
    case sp of
      TypeParam _       -> pure sp
      ConstParam c t    -> ConstParam c    <$> resolve t
      NodeParam s f x p -> NodeParam s f x <$> resolve p

instance Resolve NodeProfile where
  resolve np = do is <- traverse {-XXX: scopes-} resolve (nodeInputs np)
                  os <- traverse resolve (nodeOutputs np)
                  pure np { nodeInputs = is, nodeOutputs = os }


instance Resolve InputBinder where
  resolve ib =
    case ib of
      InputBinder b  -> InputBinder  <$> resolve b
      InputConst c t -> InputConst c <$> resolve t


instance Resolve StaticArg where
  resolve sa =
    case sa of
      TypeArg t     -> TypeArg    <$> resolve t
      ExprArg e     -> ExprArg    <$> resolveConstExpr e
      NodeArg f ni  -> NodeArg f  <$> resolve ni
      ArgRange r a  -> ArgRange r <$> resolve a



instance Resolve NodeInstDecl where
{- 
  XXX: add `ins` to scope
  resolve nid = do ins  <- resolve (nodeInstStaticInputs nid)
                   prof <- resolve (nodeInstProfile nid)
                   def  <- resolve (nodeInstDef nid)
                   pure nid { nodeInstStaticInputs = ins
                            , nodeInstProfile = prof
                            , nodeInstDef = def
                            }
-}

instance Resolve Binder where
  resolve b = do t <- resolve (binderType b)
                 c <- traverse resolve (binderClock b)
                 pure b { binderType = t, binderClock = c }

instance Resolve NodeInst where
  resolve (NodeInst x as) = NodeInst <$> resolve x <*> traverse resolve as

instance Resolve Callable where
  resolve c =
    case c of
      CallUser n  -> CallUser <$> resolveName n ANode
      CallPrim {} -> pure c


resolveConstExpr :: Expression -> ResolveM Expression
resolveConstExpr expr =
  case expr of
    ERange r e            -> ERange r <$> resolveConstExpr e
    Var x                 -> Var <$> resolveName x AConst
    Lit _                 -> pure expr
    When {}               -> bad "when"
    Tuple es              -> Tuple  <$> traverse resolveConstExpr es
    Array es              -> Array  <$> traverse resolveConstExpr es
    Select e s            -> Select <$> resolveConstExpr e <*> resolve s

    Struct x fs           ->
      do x1  <- resolveName x AType
         fs1 <- traverse (resolveField resolveConstExpr) fs
         pure (Struct x1 fs1)

    UpdateStruct x y fs   ->
      do x1  <- resolveName x AType
         y1  <- resolveName y AConst
         fs1 <- traverse (resolveField resolveConstExpr) fs
         pure (UpdateStruct x1 y1 fs1)

    WithThenElse e1 e2 e3 ->
      WithThenElse <$> resolveConstExpr e1
                   <*> resolveConstExpr e2 <*> resolveConstExpr e3

    Merge {}  -> bad "merge"
    Call {}   -> bad "call to a node"

  where
  bad = reportError . InvalidConstantExpression


resolveExpr :: Expression -> ResolveM Expression
resolveExpr expr =
  case expr of
    ERange r e            -> ERange r <$> resolveExpr e
    Var x                 -> Var <$> inferName x
    Lit _                 -> pure expr
    e1 `When` e2          -> When <$> resolveExpr e1 <*> resolve e2

    Tuple es              -> Tuple  <$> traverse resolveExpr es
    Array es              -> Array  <$> traverse resolveExpr es
    Select e s            -> Select <$> resolveExpr e <*> resolve s

    Struct x fs           ->
      do x1 <- resolveName x AType
         fs1 <- traverse (resolveField resolveExpr) fs
         pure (Struct x1 fs1)

    UpdateStruct x y fs   ->
      do x1   <- resolveName x AType
         y1   <- inferName y
         fs1  <- traverse (resolveField resolveExpr) fs
         pure (UpdateStruct x1 y1 fs1)

    WithThenElse e1 e2 e3 ->
      WithThenElse <$> resolveConstExpr e1
                   <*> resolveExpr e2 <*> resolveExpr e3

    Merge x es -> Merge <$> resolveIdent x <*> traverse resolve es
    Call f es  -> Call <$> resolve f <*> traverse resolveExpr es


instance (e ~ Expression) => Resolve (MergeCase e) where
  resolve (MergeCase c v) = MergeCase <$> resolveConstExpr c <*> resolveExpr v

instance Resolve ClockExpr where
  resolve (WhenClock r cv i) =
    WhenClock r <$> resolveConstExpr cv <*> resolveIdent i


instance Resolve NodeDecl where
  resolve x = undefined
{-
    do inps <- resolve (nodeStaticInputs x)
       withDefs (nodeStaticInputs x) $
          do prof <- resolve (nodeProfile x)


           ((resolve (nodeProfile x) <>
              (resolve (nodeContract x, nodeDef x)
                                `without` getDefs (nodeProfile x)))
           `without` getDefs (nodeStaticInputs x))
-}


instance Resolve NodeBody where
  resolve nb =
    do (cs1,constScope) <- resolveNonRecGroup constName cs
       vs1 <- undefined vs
       eqs <- mapM resolve (nodeEqns nb)
       pure nb { nodeLocals = map LocalConst cs1 ++
                                         map LocalVar   vs1
                           , nodeEqns   = eqs }
    where
    cs = [ c | LocalConst c <- nodeLocals nb ]
    vs = [ v | LocalVar   v <- nodeLocals nb ]


instance Resolve Equation where
  resolve eqn =
    case eqn of
      Assert n e   -> Assert n   <$> resolveExpr e
      Property n e -> Property n <$> resolveExpr e
      Define lhs e -> Define     <$> traverse resolve lhs <*> resolveExpr e
      IsMain _     -> pure eqn
      IVC is       -> IVC <$> traverse resolveIdent is

instance (e ~ Expression) => Resolve (LHS e) where
  resolve lhs =
    case lhs of
      LVar i      -> LVar    <$> resolveIdent i
      LSelect x e -> LSelect <$> resolve x <*> resolve e


instance (e ~ Expression) => Resolve (Selector e) where
  resolve sel =
    case sel of
      SelectField _   -> pure sel
      SelectElement e -> SelectElement <$> resolveConstExpr e
      SelectSlice e   -> SelectSlice <$> resolve e

instance (e ~ Expression) => Resolve (ArraySlice e) where
  resolve as = do s <- resolveConstExpr (arrayStart as)
                  e <- resolveConstExpr (arrayEnd as)
                  st <- traverse resolveConstExpr (arrayStep as)
                  pure as { arrayStart = s, arrayEnd = e, arrayStep = st }

instance Resolve Contract where
{-
  resolve c = resolve is `without` getDefs is
    where is = contractItems c
-}


instance Resolve ContractItem where
{-
  resolve ci =
    case ci of
      GhostConst _ mbT e -> resolve (mbT, e)
      GhostVar   b     e -> resolve (b,e)
      Assume e           -> resolve e
      Guarantee e        -> resolve e
      Mode _ mas mgs     -> resolve (mas,mgs)
      Import x as bs     -> Set.insert (ContractNS,Unqual x) (resolve (as,bs))
-}


instance Resolve ContractDecl where
  -- resolve cd = resolve (cdItems cd) `without` getDefs (cdProfile cd)



--------------------------------------------------------------------------------

newtype ResolveM a = ResolveM { unResolveM ::
  WithBase Id
    [ ExceptionT ResolveError -- state persists across exceptions
    , ReaderT    ResR
    , StateT     ResS
    ] a
  } deriving (Functor,Applicative,Monad)

-- | What's in scope for each module.
type InScope = Map (Maybe ModName) (Map Ident (Map NameSpace ResolvedName))

-- | The "scoped" part of the resolver monad
data ResR = ResR
  { resInScope  :: InScope        -- ^ What's in scope
  , resModule   :: Maybe ModName  -- ^ Use this for current definitions
  }

-- | The "mutable" part of the resolver monad
data ResS = ResS
  { resFree     :: !(Set ResolvedName)  -- ^ Free used variables
  , resNextName :: !Int                 -- ^ To generate unique names
  , resWarns    :: ![ResolveWarn]       -- ^ Warnings
  }

data ResolveError = InvalidConstantExpression String
                  | UndefinedName Name
                  | AmbiguousName Name
                  | RepeatedDefinitions [Ident]
                  | BadRecursiveDefs [Ident]

data ResolveWarn  = Shadows ResolvedName ResolvedName

-- | Report the given error, aborting the analysis.
reportError :: ResolveError -> ResolveM a
reportError e = ResolveM (raise e)

-- | Record a warning.
addWarning :: ResolveWarn -> ResolveM ()
addWarning w = ResolveM $ sets_ $ \s -> s { resWarns = w : resWarns s }

-- | Record a use of the given name.
addUse :: ResolvedName -> ResolveM ()
addUse rn = ResolveM $ sets_ $ \s -> s { resFree = Set.insert rn (resFree s) }


-- | Compute the definitions from a bunch of things,
-- checking that there are no duplicates.
-- Note that this operation is **effectful**, as it assignes unique
-- identifiers to the defined names.
defsOf :: Defines a => [a] -> ResolveM ([Set ResolvedName], InScope)
defsOf as =
  do ds  <- traverse defsOfOne as
     mp  <- traverse (traverse check) (foldr mergeDefs noDefs ds)
     mo  <- ResolveM (resModule <$> ask)
     pure (map defNames ds, Map.singleton mo mp)
  where
  check xs =
    case Set.minView xs of
      Just (a,more) | Set.null more -> pure a
      _ -> reportError (RepeatedDefinitions (map rnIdent (Set.toList xs)))

  defsOfOne a = ResolveM $
    do l <- resModule <$> ask
       sets $ \s -> let (d,n) = getDefs a l (resNextName s)
                    in (d, s { resNextName = n })

-- | Extend the current scope for the duration of the given computation.
-- The new entries shadow the existing ones.
extendScope :: InScope -> ResolveM a -> ResolveM a
extendScope ds (ResolveM m) =
  do ro <- ResolveM ask
     let new = shadowScope ds (resInScope ro)
     traverse_ (traverse_ (traverse_ reportShadow)) (gotShadowed new)
     ResolveM (local ro { resInScope = newScope new } m)
  where
  reportShadow old =
    case mb of
      Nothing -> panic "extendScope" [ "Shadowed, but not?"
                                     , "*** Name: " ++ showPP old ]
      Just new ->
        case rnThing old of
          AVal -> reportError (RepeatedDefinitions [rnIdent new, rnIdent old])
          _    -> addWarning (Shadows new old)

    where
    mb = do ids <- Map.lookup (rnModule old) ds
            ths <- Map.lookup (rnIdent old) ids
            Map.lookup (thingNS (rnThing old)) ths



-- | Extend the definitions in the second scope with the first.
-- New entries in the same namespace "shadow" existing ones.
shadowScope :: InScope -> InScope -> WithShadows InScope
shadowScope = joinWith (joinWith joinThings)
  where
  joinWith :: (Ord k, Ord k1) =>
                ShadowFun (Map k v) -> ShadowFun (Map k1 (Map k v))
  joinWith f m1 m2 =
    let mp = Map.mergeWithKey (\_ a b -> Just (f a b)) noShadow noShadow m1 m2
    in WS { newScope    = newScope <$> mp
          , gotShadowed = Map.filter (not . Map.null) (gotShadowed <$> mp)
          }

  noShadow m = fmap (\a -> WS { newScope = a, gotShadowed = Map.empty }) m

  joinThings :: ShadowFun (Map NameSpace ResolvedName)
  joinThings as bs =
    WS { newScope    = Map.union as bs
       , gotShadowed = Map.intersectionWith (\_ old -> old) as bs
       }


data WithShadows a = WS { newScope :: a, gotShadowed :: a }
type ShadowFun a   = a -> a -> WithShadows a



-- | Specify the location of names for the scope of the given computation.
withModName :: Maybe ModName -> ResolveM a -> ResolveM a
withModName l (ResolveM m) =
  ResolveM $ mapReader (\ro -> ro { resModule = l }) m

-- | Resolve something but do not modify the state.  Instead the dependencies
-- of the thing are returned.
resolveWithFree :: Resolve a => a -> ResolveM (a, Set ResolvedName)
resolveWithFree a =
  do free <- ResolveM $ sets $ \s -> (resFree s, s { resFree = Set.empty })
     a1   <- resolve a
     thisFree <- ResolveM $ sets $ \s -> (resFree s, s { resFree = free })
     pure (a1, thisFree)


--------------------------------------------------------------------------------
-- Resolving of names

-- | Figure out what a name of the given flavor refers to.
resolveName :: Name -> Thing -> ResolveM Name
resolveName nm th =
  do mb <- lkpIdent m th i
     case mb of
       Nothing -> reportError (UndefinedName nm)
       Just rn -> do addUse rn
                     pure nm -- XXX: use `rn`

  where
  (m,i) = case nm of
            Unqual ide -> (Nothing , ide)
            Qual _ q t -> (Just (Module q), identFromText t)


-- | Figure out what the given name referes to (either value or a constnat).
inferName :: Name -> ResolveM Name
inferName nm =
  do mb1 <- lkpIdent m AConst i
     mb2 <- lkpIdent m AVal  i
     case (mb1,mb2) of
       (Nothing, Nothing) -> reportError (UndefinedName nm)
       (Just _, Just _)   -> reportError (AmbiguousName nm)
       (Just rn,Nothing)  -> do addUse rn
                                pure nm -- XXX: use rn
       (Nothing, Just rn) -> do addUse rn
                                pure nm -- XXX: use rn
  where
  (m,i) = case nm of
            Unqual ide -> (Nothing, ide)
            Qual _ q t -> (Just (Module q), identFromText t)


-- | Figure out what the given identifier refers (value or constnat)
resolveIdent :: Ident -> ResolveM Ident
resolveIdent i =
  do mb1 <- lkpIdent Nothing AConst i
     mb2 <- lkpIdent Nothing AVal  i
     case (mb1,mb2) of
       (Nothing, Nothing) -> reportError (UndefinedName (Unqual i))
       (Just _, Just _)   -> reportError (AmbiguousName (Unqual i))
       (Just rn,Nothing)  -> do addUse rn
                                pure i -- XXX: use rn
       (Nothing, Just rn) -> do addUse rn
                                pure i -- XXX: use rn

-- | Lookup something in the current scope.
lkpIdent :: Maybe ModName -> Thing -> Ident -> ResolveM (Maybe ResolvedName)
lkpIdent loc th i =
  do scope <- ResolveM (resInScope <$> ask)
     pure $ do defs   <- Map.lookup loc scope
               things <- Map.lookup i   defs
               Map.lookup (thingNS th) things







