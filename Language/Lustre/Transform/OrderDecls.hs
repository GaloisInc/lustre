{-# Language DataKinds, GeneralizedNewtypeDeriving, TypeFamilies #-}
module Language.Lustre.Transform.OrderDecls (orderTopDecls) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe(mapMaybe,isJust)
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import Data.Foldable(traverse_)
import Data.Coerce(coerce)
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Pretty(showPP)
import Language.Lustre.Panic(panic)
import Language.Lustre.Defines


orderTopDecls :: [TopDecl] -> [TopDecl]
orderTopDecls = undefined -- concatMap orderRec . undefined

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

{- | Order an unordered set of declarations, in dependency order.
The result is a dependency-ordered sequence of strongly-connected
components, and the new names introduced by the declarations -}
resolveGroup ::
  (Defines a, Resolve a) => [a] -> ([SCC a] -> ResolveM b) -> ResolveM b
resolveGroup ds k =
  do (namess, scope) <- defsOf ds
     extendScope scope $
      do resolved <- traverse resolveWithFree ds

         let mkRep i ns = [ (n,i) | n <- Set.toList ns ]
             keys       = [ 0 .. ] :: [Int]
             repFor     = (`Map.lookup` mp)
                where mp = Map.fromList $ concat $ zipWith mkRep keys namess
             mkNode i (a,us) = (a, i, mapMaybe repFor (Set.toList us))
             comps = stronglyConnComp (zipWith mkNode keys resolved)

         k comps


-- | Resolve a list of declaratons, where the results of each are in scope
-- of the next. The continuation is then executed in the newly computed scope.
-- Note that value identifiers still cannot shadow each other
-- so multiple declarations should still result in errors.
resolveOrderedGroup ::
  (Defines a, Resolve a) => [a] -> ([a] -> ResolveM b) -> ResolveM b
resolveOrderedGroup ds0 k = go [] ds0
  where
  go done ds =
    case ds of
      [] -> k (reverse done)
      d : more ->
        do d1        <- resolve d
           (_,scope) <- defsOf [d]
           extendScope scope (go (d1 : done) more)



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
  (a -> Ident)              {- ^ Use this name when reporting errors -} ->
  [a]                       {- ^ Group of declarations -} ->
  ([a] -> ResolveM b)       {- ^ Run this continuation in the new scope -} ->
  ResolveM b
resolveNonRecGroup isRec xs k =
  resolveGroup xs $ \comps -> k =<< noRec isRec comps



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
      NodeParam s f x p -> NodeParam s f x <$> resolveProfile p pure


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


resolveProfile :: NodeProfile -> (NodeProfile -> ResolveM a) -> ResolveM a
resolveProfile prof k =
  resolveOrderedGroup (nodeInputs prof) $ \ins ->
  resolveOrderedGroup (coerce (nodeOutputs prof)) $ \outs ->
  k prof { nodeInputs = ins, nodeOutputs = coerce (outs :: [ValBinder]) }




instance Resolve NodeInstDecl where
  resolve nid =
    withModName Nothing $
    resolveOrderedGroup (nodeInstStaticInputs nid) $ \sinps ->
    let k prof = do def <- resolve (nodeInstDef nid)
                    pure nid { nodeInstStaticInputs = sinps
                             , nodeInstProfile      = prof
                             , nodeInstDef          = def
                             }
    in
    case nodeInstProfile nid of
      Nothing -> k Nothing
      Just prof -> resolveProfile prof (k . Just)

instance Resolve Binder where
  resolve b = do t <- resolve (binderType b)
                 c <- traverse resolve (binderClock b)
                 pure b { binderType = t, binderClock = c }

instance Resolve ValBinder where
  resolve (ValBinder b) = ValBinder <$> resolve b

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
  resolve nd =
    resolveOrderedGroup (nodeStaticInputs nd) $ \sinps ->
    resolveProfile (nodeProfile nd)           $ \prof ->
    do ctr  <- traverse resolve (nodeContract nd)
       body <- traverse resolve (nodeDef nd)
       pure nd { nodeStaticInputs = sinps
               , nodeProfile      = prof
               , nodeContract     = ctr
               , nodeDef          = body
               }

instance Resolve NodeBody where
  resolve nb =
    -- We do constants before local variables.
    -- This matters if a local variable shadows a global constant.
    -- In that case the, the constant definitions would resolve correctly.
    -- XXX: It is a bit questionable if allowing such definitios is a good idea.
    resolveNonRecGroup getIdent cs $ \cs1 ->
    resolveNonRecGroup getIdent vs $ \vs1 ->
    do eqs <- traverse resolve (nodeEqns nb)
       pure nb { nodeLocals = cs1 ++ vs1, nodeEqns = eqs }
    where
    cs = [ LocalConst c | LocalConst c <- nodeLocals nb ]
    vs = [ LocalVar v   | LocalVar   v <- nodeLocals nb ]
    getIdent x = case x of
                  LocalConst c -> constName c
                  LocalVar b   -> binderDefines b

instance Resolve LocalDecl where
  resolve ld =
    case ld of
      LocalConst c -> LocalConst <$> resolve c
      LocalVar   v -> LocalVar   <$> resolve v


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

newtype ResolveM a = ResolveM { _unResolveM ::
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


-- | Various things that can go wrong when resolving names.
data ResolveError = InvalidConstantExpression String
                  | UndefinedName Name
                  | AmbiguousName Name
                  | RepeatedDefinitions [Ident]
                  | BadRecursiveDefs [Ident]

-- | Potential problems, but not fatal.
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
     a <- ResolveM (local ro { resInScope = newScope new } m)
     -- remove uses of the locally added variables as they are not free
     let isHere x = isJust $ do is <- Map.lookup (rnModule x) ds
                                ns <- Map.lookup (rnIdent x) is
                                Map.lookup (thingNS (rnThing x)) ns
     ResolveM $ sets_
              $ \s -> s { resFree = Set.filter (not . isHere) (resFree s) }
     pure a


  where
  reportShadow old =
    case mb of
      Nothing -> panic "extendScope" [ "Shadowed, but not?"
                                     , "*** Name: " ++ showPP old ]
      Just new ->
        case rnThing old of
          -- value identifiers cannot be shadowed
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

-- | Resolve something, and also return its free variables.
-- Note that the free variables are also saved in the state of the monad.
resolveWithFree :: Resolve a => a -> ResolveM (a, Set ResolvedName)
resolveWithFree a =
  do free     <- ResolveM $ sets $ \s -> (resFree s, s { resFree = Set.empty })
     a1       <- resolve a
     newFree  <- ResolveM $ sets$ \s ->
                  let newFree = resFree s
                  in (newFree, s { resFree = Set.union newFree free })
     pure (a1, newFree)


--------------------------------------------------------------------------------
-- Resolving of names

-- | Figure out what a name of the given flavor refers to.
resolveName :: Name -> Thing -> ResolveM Name
resolveName nm th =
  case nm of
    Resolved ResolvedName { rnThing = t }
      | t == th -> pure nm
      | otherwise -> panic "resolveName"
                       [ "Resolved name in the wrong location:"
                       , "*** Expected:" ++ showPP th
                       , "*** Got:     " ++ showPP t
                       ]
    Unqual ide  -> doResolve Nothing ide
    Qual _ q t  -> doResolve (Just (Module q)) (identFromText t)
  where
  doResolve m i =
    do mb <- lkpIdent m th i
       case mb of
         Nothing -> reportError (UndefinedName nm)
         Just rn -> do addUse rn
                       pure (Resolved rn)


-- | Figure out what the given name referes to (either value or a constnat).
inferName :: Name -> ResolveM Name
inferName nm =
  case nm of
    Resolved {} -> pure nm
    Unqual ide -> doResolve Nothing ide
    Qual _ q t -> doResolve (Just (Module q)) (identFromText t)
  where
  doResolve m i =
    do mb1 <- lkpIdent m AConst i
       mb2 <- lkpIdent m AVal  i
       case (mb1,mb2) of
         (Nothing, Nothing) -> reportError (UndefinedName nm)
         (Just _, Just _)   -> reportError (AmbiguousName nm)
         (Just rn,Nothing)  -> do addUse rn
                                  pure (Resolved rn)
         (Nothing, Just rn) -> do addUse rn
                                  pure (Resolved rn)


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







