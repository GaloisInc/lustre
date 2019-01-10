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
      do resolved <- zipWithM resolveWithFree namess ds

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
  go done todo =
    case todo of
      [] -> k (reverse done)
      d : more ->
        do (~[ds],scope) <- defsOf [d]
           d1            <- resolveDef ds d
           extendScope scope (go (d1 : done) more)



-- | Check that none of the given SCC-s are recursive.
noRec :: (a -> Ident) {- ^ Pick an identifier to use for the given entry.
                           This is used for error reporting. -} ->
          [SCC a] ->
          ResolveM [a]
noRec nm = traverse check
  where
  check x =
    case x of
      AcyclicSCC a -> pure a
      CyclicSCC as -> reportError (BadRecursiveDefs (map (identOrigName . nm) as))


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

  -- | Rsolve something that may define things.
  -- The first argument specified how to rewrite the defining sites.
  resolveDef :: Set OrigName -> t -> ResolveM t

-- | Resolve something that only uses names, but does not define any.
resolve :: Resolve t => t -> ResolveM t
resolve = resolveDef Set.empty

instance Resolve TopDecl where
  resolveDef ds ts =
    case ts of
      DeclareType td      -> DeclareType     <$> resolveDef ds td
      DeclareConst cd     -> DeclareConst    <$> resolveDef ds cd
      DeclareNode nd      -> DeclareNode     <$> resolveDef ds nd
      DeclareNodeInst nid -> DeclareNodeInst <$> resolveDef ds nid
      DeclareContract cd  -> DeclareContract <$> resolveDef ds cd

instance Resolve TypeDecl where
  resolveDef ds t =
    do t1 <- traverse (resolveDef ds) (typeDef t)
       pure TypeDecl { typeName = lkpDef ds AType (typeName t)
                     , typeDef  = t1 }

instance Resolve TypeDef where
  resolveDef ds td =
    case td of
      IsType t    -> IsType <$> resolve t
      IsEnum cs   -> pure (IsEnum (map (lkpDef ds AConst) cs))
      IsStruct fs -> IsStruct <$> traverse resolve fs

instance Resolve FieldType where
  resolveDef _ ft = do t1 <- resolve (fieldType ft)
                       e1 <- traverse resolveConstExpr (fieldDefault ft)
                       pure ft { fieldType = t1, fieldDefault = e1 }

resolveField :: (e -> ResolveM e) -> Field e -> ResolveM (Field e)
resolveField res (Field l e) = Field l <$> res e

instance Resolve Type where
  resolveDef _ ty =
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
  resolveDef ds cd =
    do t <- traverse resolve (constType cd)
       e <- traverse resolveConstExpr (constDef cd)
       pure ConstDef { constName = lkpDef ds AConst (constName cd)
                     , constType = t
                     , constDef  = e }


instance Resolve StaticParam where
  resolveDef ds sp =
    case sp of
      TypeParam p       -> pure (TypeParam (lkpDef ds AType p))
      ConstParam c t    -> ConstParam (lkpDef ds AConst c) <$> resolve t
      NodeParam s f x p ->
        NodeParam s f (lkpDef ds ANode x) <$> resolveProfile p pure


instance Resolve InputBinder where
  resolveDef ds ib =
    case ib of
      InputBinder b  -> InputBinder  <$> resolveDef ds b
      InputConst c t -> InputConst (lkpDef ds AConst c) <$> resolve t

instance Resolve Binder where
  resolveDef ds b =
    do t <- resolve (binderType b)
       c <- traverse resolve (binderClock b)
       pure Binder { binderDefines = lkpDef ds AVal (binderDefines b)
                   , binderType    = t
                   , binderClock   = c }




instance Resolve StaticArg where
  resolveDef _ sa =
    case sa of
      TypeArg t     -> TypeArg    <$> resolve t
      ExprArg e     -> ExprArg    <$> resolveConstExpr e
      NodeArg f ni  -> NodeArg f  <$> resolve ni
      ArgRange r a  -> ArgRange r <$> resolve a


resolveProfile :: NodeProfile -> (NodeProfile -> ResolveM a) -> ResolveM a
resolveProfile prof k =
  resolveOrderedGroup (nodeInputs prof) $ \ins ->
  resolveOrderedGroup (nodeOutputs prof) $ \outs ->
  k NodeProfile { nodeInputs = ins, nodeOutputs = outs }




instance Resolve NodeInstDecl where
  resolveDef ds nid =
    inLocalScope $
    resolveOrderedGroup (nodeInstStaticInputs nid) $ \sinps ->
    let k prof = do def <- resolve (nodeInstDef nid)
                    let nm = lkpDef ds ANode (nodeInstName nid)
                    pure nid { nodeInstName         = nm
                             , nodeInstStaticInputs = sinps
                             , nodeInstProfile      = prof
                             , nodeInstDef          = def
                             }
    in
    case nodeInstProfile nid of
      Nothing   -> k Nothing
      Just prof -> resolveProfile prof (k . Just)


instance Resolve NodeInst where
  resolveDef _ (NodeInst x as) = NodeInst <$> resolve x <*> traverse resolve as

instance Resolve Callable where
  resolveDef _ c =
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
  resolveDef _ (MergeCase c v) =
    MergeCase <$> resolveConstExpr c <*> resolveExpr v

instance Resolve ClockExpr where
  resolveDef _ (WhenClock r cv i) =
    WhenClock r <$> resolveConstExpr cv <*> resolveIdent i


instance Resolve NodeDecl where
  resolveDef ds nd =
    inLocalScope $
    resolveOrderedGroup (nodeStaticInputs nd) $ \sinps ->
    resolveProfile (nodeProfile nd)           $ \prof ->
    do ctr  <- traverse resolve (nodeContract nd)
       body <- traverse resolve (nodeDef nd)
       pure nd { nodeName         = lkpDef ds ANode (nodeName nd)
               , nodeStaticInputs = sinps
               , nodeProfile      = prof
               , nodeContract     = ctr
               , nodeDef          = body
               }

instance Resolve NodeBody where
  resolveDef _ nb =
    -- We do constants before local variables.
    -- This matters if a local variable shadows a global constant.
    -- In that case the, the constant definitions would resolve correctly.
    -- XXX: It is a bit questionable if allowing such definitios is a good idea.
    resolveNonRecGroup getIdent cs $ \cs1 ->
    resolveNonRecGroup getIdent vs $ \vs1 ->
    do eqs <- traverse resolve (nodeEqns nb)
       pure NodeBody { nodeLocals = cs1 ++ vs1, nodeEqns = eqs }
    where
    cs = [ LocalConst c | LocalConst c <- nodeLocals nb ]
    vs = [ LocalVar v   | LocalVar   v <- nodeLocals nb ]
    getIdent x = case x of
                  LocalConst c -> constName c
                  LocalVar b   -> binderDefines b

instance Resolve LocalDecl where
  resolveDef ds ld =
    case ld of
      LocalConst c -> LocalConst <$> resolveDef ds c
      LocalVar   v -> LocalVar   <$> resolveDef ds v


instance Resolve Equation where
  resolveDef _ eqn =
    case eqn of
      Assert n e   -> Assert n   <$> resolveExpr e
      Property n e -> Property n <$> resolveExpr e
      Define lhs e -> Define     <$> traverse resolve lhs <*> resolveExpr e
      IsMain _     -> pure eqn
      IVC is       -> IVC <$> traverse resolveIdent is

instance (e ~ Expression) => Resolve (LHS e) where
  resolveDef _ lhs =
    case lhs of
      LVar i      -> LVar    <$> resolveIdent i
      LSelect x e -> LSelect <$> resolve x <*> resolve e


instance (e ~ Expression) => Resolve (Selector e) where
  resolveDef _ sel =
    case sel of
      SelectField _   -> pure sel
      SelectElement e -> SelectElement <$> resolveConstExpr e
      SelectSlice e   -> SelectSlice   <$> resolve e

instance (e ~ Expression) => Resolve (ArraySlice e) where
  resolveDef _ as =
    do s  <- resolveConstExpr (arrayStart as)
       e  <- resolveConstExpr (arrayEnd as)
       st <- traverse resolveConstExpr (arrayStep as)
       pure ArraySlice { arrayStart = s, arrayEnd = e, arrayStep = st }

instance Resolve Contract where
  resolveDef _ _ = undefined
{-
  resolve c = resolve is `without` getDefs is
    where is = contractItems c
-}


instance Resolve ContractItem where
  resolveDef _ _ = undefined
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
  resolveDef _ _ = undefined
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
type InScope = Map (Maybe ModName) (Map NameSpace OrigName)

-- | The "scoped" part of the resolver monad
data ResR = ResR
  { resInScope  :: InScope        -- ^ What's in scope
  , resModule   :: Maybe ModName  -- ^ Use this for current definitions
  }

-- | The "mutable" part of the resolver monad
data ResS = ResS
  { resFree     :: !(Set OrigName)       -- ^ Free used variables
  , resNextName :: !Int                 -- ^ To generate unique names
  , resWarns    :: ![ResolveWarn]       -- ^ Warnings
  }


-- | Various things that can go wrong when resolving names.
data ResolveError = InvalidConstantExpression String
                  | UndefinedName Name
                  | AmbiguousName Name OrigName OrigName
                  | RepeatedDefinitions [OrigName]
                  | BadRecursiveDefs [OrigName]

-- | Potential problems, but not fatal.
data ResolveWarn  = Shadows OrigName OrigName

-- | Report the given error, aborting the analysis.
reportError :: ResolveError -> ResolveM a
reportError e = ResolveM (raise e)

-- | Record a warning.
addWarning :: ResolveWarn -> ResolveM ()
addWarning w = ResolveM $ sets_ $ \s -> s { resWarns = w : resWarns s }

-- | Record a use of the given name.
addUse :: OrigName -> ResolveM ()
addUse rn = ResolveM $ sets_ $ \s -> s { resFree = Set.insert rn (resFree s) }


-- | Compute the definitions from a bunch of things,
-- checking that there are no duplicates.
-- Note that this operation is **effectful**, as it assignes unique
-- identifiers to the defined names.
defsOf :: Defines a => [a] -> ResolveM ([Set OrigName], InScope)
defsOf as =
  do ds  <- traverse defsOfOne as
     mp  <- traverse check (foldr mergeDefs noDefs ds)
     mo  <- ResolveM (resModule <$> ask)
     pure (map defNames ds, Map.singleton mo mp)
  where
  check xs =
    case Set.minView xs of
      Just (a,more) | Set.null more -> pure a
      _ -> reportError (RepeatedDefinitions (Set.toList xs))

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
     traverse_ (traverse_ reportShadow) (gotShadowed new)
     a <- ResolveM (local ro { resInScope = newScope new } m)
     -- remove uses of the locally added variables as they are not free
     let isHere x = isJust $ do is <- Map.lookup (rnModule x) ds
                                let ns = thingNS (rnThing x)
                                Map.lookup ns is
     ResolveM $ sets_
              $ \s -> s { resFree = Set.filter (not . isHere) (resFree s) }
     pure a


  where
  reportShadow :: OrigName -> ResolveM ()
  reportShadow old =
    case mb of
      Nothing -> panic "extendScope" [ "Shadowed, but not?"
                                     , "*** Name: " ++ showPP old ]
      Just new ->
        case rnThing old of
          -- value identifiers cannot be shadowed
          AVal -> reportError (RepeatedDefinitions [new, old])
          _    -> addWarning (Shadows new old)

    where
    mb = do ids <- Map.lookup (rnModule old) ds
            Map.lookup (thingNS (rnThing old)) ids



-- | Extend the definitions in the second scope with the first.
-- New entries in the same namespace "shadow" existing ones.
shadowScope :: InScope -> InScope -> WithShadows InScope
shadowScope = joinWith joinThings
  where
  joinWith :: (Ord k, Ord k1) =>
                ShadowFun (Map k v) -> ShadowFun (Map k1 (Map k v))
  joinWith f m1 m2 =
    let mp = Map.mergeWithKey (\_ a b -> Just (f a b)) noShadow noShadow m1 m2
    in WS { newScope    = newScope <$> mp
          , gotShadowed = Map.filter (not . Map.null) (gotShadowed <$> mp)
          }

  noShadow m = fmap (\a -> WS { newScope = a, gotShadowed = Map.empty }) m

  joinThings :: ShadowFun (Map NameSpace OrigName)
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

inLocalScope :: ResolveM a -> ResolveM a
inLocalScope = withModName Nothing

-- | Resolve something, and also return its free variables.
-- Note that the free variables are also saved in the state of the monad.
resolveWithFree :: Resolve a => Set OrigName -> a -> ResolveM (a, Set OrigName)
resolveWithFree ds a =
  do free     <- ResolveM $ sets $ \s -> (resFree s, s { resFree = Set.empty })
     a1       <- resolveDef ds a
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
    Unqual ide  ->
      case identResolved ide of
        Nothing -> doResolve Nothing ide
        Just OrigName { rnThing = t }
          | t == th -> pure nm
          | otherwise -> panic "resolveName"
                           [ "Resolved name in the wrong location:"
                           , "*** Expected:" ++ showPP th
                           , "*** Got:     " ++ showPP t
                           ]
    Qual _ q t  -> doResolve (Just (Module q)) (identFromText t)
  where
  doResolve m i =
    do mb <- lkpIdent m th i
       case mb of
         Nothing -> reportError (UndefinedName nm)
         Just rn -> do addUse rn
                       pure (Unqual i { identResolved = Just rn })


-- | Figure out what the given name referes to (either value or a constnat).
inferName :: Name -> ResolveM Name
inferName nm =
  case nm of
    Unqual ide ->
      case identResolved ide of
        Nothing -> doResolve Nothing ide
        Just _  -> pure nm
    Qual _ q t -> doResolve (Just (Module q)) (identFromText t)
  where
  doResolve m i =
    do mb1 <- lkpIdent m AConst i
       mb2 <- lkpIdent m AVal  i
       let toId rn = pure (Unqual i { identResolved = Just rn })
       case (mb1,mb2) of
         (Nothing, Nothing) -> reportError (UndefinedName nm)
         (Just p, Just q)   -> reportError (AmbiguousName nm p q)
         (Just rn,Nothing)  -> do addUse rn
                                  toId rn
         (Nothing, Just rn) -> do addUse rn
                                  toId rn



-- | Figure out what the given identifier refers (value or constnat)
resolveIdent :: Ident -> ResolveM Ident
resolveIdent i =
  do mb1 <- lkpIdent Nothing AConst i
     mb2 <- lkpIdent Nothing AVal  i
     case (mb1,mb2) of
       (Nothing, Nothing) -> reportError (UndefinedName (Unqual i))
       (Just p, Just q)   -> reportError (AmbiguousName (Unqual i) p q)
       (Just rn,Nothing)  -> do addUse rn
                                pure i { identResolved = Just rn }
       (Nothing, Just rn) -> do addUse rn
                                pure i { identResolved = Just rn }

-- | Lookup something in the current scope.
lkpIdent :: Maybe ModName -> Thing -> Ident -> ResolveM (Maybe OrigName)
lkpIdent loc th i =
  do scope <- ResolveM (resInScope <$> ask)
     pure $ do defs   <- Map.lookup loc scope
               nm     <- Map.lookup (thingNS th) defs
               guard (identText i == identText (rnIdent nm))
               pure nm

-- | Resolve a name in a defining position.
lkpDef :: Set OrigName -> Thing -> Ident -> Ident
lkpDef ds th i = case Set.minView (Set.filter matches ds) of
                   Just (a,_) -> i { identResolved = Just a }
                   _ -> panic "lkpDef" [ "Missing identifier for defining site"
                                       , "*** Identifier: " ++ show i
                                       , "*** Context: " ++ show th
                                       ]
  where
  matches j = rnThing j == th && identText (rnIdent j) == identText i





