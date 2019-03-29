{-# Language OverloadedStrings, Rank2Types #-}
module Language.Lustre.TypeCheck where

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (find)
import Control.Monad(when,unless,zipWithM_,zipWithM,replicateM)
import Text.PrettyPrint as PP
import Data.List(group,sort)
import Data.Traversable(for)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic
import Language.Lustre.Monad(LustreM)
import Language.Lustre.TypeCheck.Monad
import Language.Lustre.TypeCheck.Constraint
import Language.Lustre.TypeCheck.Arity


type TypeError = Doc
type TypeWarn  = Doc


-- | Assumes that the declarations are in dependency order.
quickCheckDecls :: [TopDecl] -> LustreM [TopDecl]
quickCheckDecls ds = runTC (go ds)
  where
  go xs = case xs of
            [] -> pure []
            x : more -> do (y,ys) <- checkTopDecl x (go more)
                           pure (y:ys)


checkTopDecl :: TopDecl -> M a -> M (TopDecl,a)
checkTopDecl td m =
  case td of
    DeclareType tyd -> apFstM DeclareType (checkTypeDecl tyd m)
    DeclareConst cd -> apFstM DeclareConst (checkConstDef cd m)
    DeclareNode nd  -> apFstM DeclareNode (checkNodeDecl nd m)
    DeclareNodeInst _nid -> notYetImplemented "node instances"
    DeclareContract {} -> notYetImplemented "top-level contract"


checkTypeDecl :: TypeDecl -> M a -> M (TypeDecl, a)
checkTypeDecl td m =
  case typeDef td of
    Nothing -> addFst td $ withNamedType (typeName td) AbstractTy m
    Just dec ->
      case dec of

        IsEnum is ->
          do let nty    = NamedType (Unqual ti)
                 addE i = withConst i nty
                 ty     = EnumTy (Set.fromList (map identOrigName is))
             addFst td (withNamedType ti ty (foldr addE m is))

        IsStruct fs ->
          do fs1 <- mapM checkFieldType fs
             mapM_ checkDup $ group $ sort $ map fieldName fs1
             let ty  = StructTy fs1
                 newTD = td { typeDef = Just (IsStruct fs1) }
             addFst newTD (withNamedType ti ty m)

        IsType t ->
           do t1 <- checkType t
              t2 <- tidyType t1
              let newTD = td { typeDef = Just (IsType t1) }
              addFst newTD (withNamedType ti (AliasTy t2) m)
  where
  ti = typeName td

  checkDup xs =
    case xs of
      [] -> pure ()
      [_] -> pure ()
      x : _ ->
        reportError $ nestedError
          "Multiple fields with the same name." $
          [ "Struct:" <+> pp (typeName td)
          , "Field:" <+> pp x
          ] ++ [ "Location:" <+> pp (range f) | f <- xs ]


checkFieldType :: FieldType -> M FieldType
checkFieldType f =
  do let t = fieldType f
     t1 <- checkType t
     d1 <- case fieldDefault f of
             Nothing -> pure Nothing
             Just e  -> Just <$> checkConstExpr e t
     pure f { fieldType = t1, fieldDefault = d1 }

checkNodeDecl :: NodeDecl -> M a -> M (NodeDecl,a)
checkNodeDecl nd k =
  do newNd <- check
     addFst newNd
       $ withNode NodeInfo
                    { niName         = nodeName newNd
                    , niSafety       = nodeSafety newNd
                    , niType         = nodeType newNd
                    , niStaticParams = nodeStaticInputs newNd
                    , niProfile      = nodeProfile newNd
                    }
                  k
  where
  check :: M NodeDecl
  check =
    inRange (range (nodeName nd)) $
    allowTemporal (nodeType nd == Node) $
    allowUnsafe   (nodeSafety nd == Unsafe) $
    do (ps,(prof,bod)) <-
          checkStaticParams (nodeStaticInputs nd) $
          do when (nodeExtern nd) $
               case nodeDef nd of
                 Just _ -> reportError $ nestedError
                           "Extern node with a definition."
                           ["Node:" <+> pp (nodeName nd)]
                 Nothing -> pure ()
             let prof = nodeProfile nd
             (ins,(outs,bod)) <-
                checkInputBinders  (nodeInputs prof) $
                checkOutputBinders (nodeOutputs prof) $
                do case nodeContract nd of
                     Nothing -> pure ()
                     Just _  -> notYetImplemented "Node contracts"

                   case nodeDef nd of
                     Nothing ->
                        do unless (nodeExtern nd) $ reportError $ nestedError
                                  "Missing node definition"
                                  ["Node:" <+> pp (nodeName nd)]
                           pure Nothing
                     Just b -> Just <$> checkNodeBody b

             let newProf = NodeProfile { nodeInputs = ins
                                       , nodeOutputs = outs
                                       }
             solveConstraints  -- XXX: we can store constraints on constants
                               -- and abstact types in the node.

             bod1 <- traverse zonkBody bod

             -- XXX: contract
             pure (newProf, bod1)

       pure nd { nodeStaticInputs = ps, nodeProfile = prof, nodeDef = bod }

checkStaticParam :: StaticParam -> M a -> M (StaticParam,a)
checkStaticParam sp m =
  case sp of
    TypeParam t ->
      do a <- withNamedType t AbstractTy m
         pure (TypeParam t, a)

    ConstParam x t ->
      do t1 <- checkType t
         a <- withConst x t1 m
         pure (ConstParam x t1, a)

    NodeParam safe fun f prof ->
      do (is,(os,_)) <- checkInputBinders (nodeInputs prof) $
                        checkOutputBinders (nodeOutputs prof) $
                        pure ()
         let prof1 = NodeProfile { nodeInputs = is, nodeOutputs = os }
             info = NodeInfo { niName = f
                             , niSafety = safe
                             , niType   = fun
                             , niStaticParams = []
                             , niProfile = prof1
                             }
         a <- withNode info m
         pure (NodeParam safe fun f prof1, a)


checkStaticParams :: [StaticParam] -> M a -> M ([StaticParam],a)
checkStaticParams = checkNested checkStaticParam

checkStaticArg :: StaticArg -> StaticParam -> M (StaticArg, StaticEnv)
checkStaticArg arg para =
  case arg of
    ArgRange r a1 -> inRange r (checkStaticArg a1 para)

    TypeArg t ->
      case para of
        TypeParam i ->
          do t1 <- checkType t
             pure (TypeArg t1, sType i t1)
        _ -> mismatch

    ExprArg e ->
      case para of
        ConstParam x t ->
          do e1 <- checkConstExpr e t
             pure (ExprArg e1, sConst x e1)
        _ -> mismatch

    NodeArg notationTy ni ->
      case para of
        NodeParam safe fun _ prof ->
          do ni1 <- checkStaticNodeArg ni safe fun prof
             pure (NodeArg notationTy ni1, sEmpty)
        _ -> mismatch
  where
  mismatch = reportError $ nestedError
             "Invalid static argument."
              [ "Expected:" <+> pDoc
              , "Got:" <+> aDoc
              ]

  aDoc = case arg of
           ExprArg {} -> "a constant expression"
           TypeArg {} -> "a type"
           NodeArg {} -> "a node"
           ArgRange {} -> panic "aDoc" ["Unexpected `ArgRange`"]

  pDoc = case para of
           TypeParam {}  -> "a type"
           ConstParam {} -> "a constant expression"
           NodeParam {}  -> "a node"


checkStaticNodeArg ::
  NodeInst -> Safety -> NodeType -> NodeProfile -> M NodeInst
checkStaticNodeArg (NodeInst c as) safe fun prof =
  case c of
    CallUser f ->
      do (ni,iprof) <- prepUserNodeInst f as safe fun
         checkStaticArgTypes iprof prof
         pure ni

    -- The prims are all safe so we don't need to pass the safety
    CallPrim _r _op ->
      notYetImplemented "Passing primitives as static arguments."

prepUserNodeInst ::
  Name -> [StaticArg] -> Safety -> NodeType -> M (NodeInst, NodeProfile)
prepUserNodeInst f as safe fun =
  do fi <- lookupNodeInfo f
     inRange (range f) $
       do checkSafetyType fi safe fun
          checkEnoughStaticArgs fi as
          (as1,envs) <- unzip <$>
                        zipWithM checkStaticArg as (niStaticParams fi)
          let env = sJoin envs
              iprof = instantiateProfile env (niProfile fi)
          pure (NodeInst (CallUser f) as1, iprof)



checkStaticArgTypes :: NodeProfile -> NodeProfile -> M ()
checkStaticArgTypes actual expected =
  do unless (haveInNum == needInNum) $
        reportError $ nestedError
          "Incorrect number of inputs."
          [ "Parameter has" <+> int needInNum <+> "inputs."
          , "Given argument has" <+> int haveInNum <+> "inputs."
          ]
     unless (haveOutNum == needOutNum) $
        reportError $ nestedError
          "Incorrect number of outputs."
          [ "Parameter has" <+> int needOutNum <+> "outputs."
          , "Given argument has" <+> int haveOutNum <+> "outputs."
          ]
     zipWithM_ checkIn  (nodeInputs actual)  (nodeInputs  expected)
     zipWithM_ checkOut (nodeOutputs actual) (nodeOutputs expected)

  where
  haveInNum = length (nodeInputs actual)
  haveOutNum = length (nodeOutputs actual)
  needInNum = length (nodeInputs expected)
  needOutNum = length (nodeOutputs expected)

  checkIn arg param =
    case (arg,param) of
      (InputConst _ t, InputConst _ t1) -> ensure (Subtype t1 t)
      (InputBinder b, InputBinder b1) -> subCType (cTypeOf b1) (cTypeOf b)
      (InputBinder {}, InputConst {}) ->
        reportError "Expected a constant input."
      (InputConst {}, InputBinder {}) ->
        reportError "Unexpected constant input." -- XXX: perhaps this is ok?

  checkOut arg param = subCType (cTypeOf arg) (cTypeOf param)

cTypeOf :: Binder -> CType
cTypeOf b = CType { cType  = binderType b
                  , cClock = case binderClock b of
                               Nothing -> BaseClock
                               Just c  -> KnownClock c }




--------------------------------------------------------------------------------
{- Example:

f <<const n : int>> (x : Array n bool) returns (y : int)
g <<node z (x : Array 2 bool) returns (y : int)>> (...) returns (...)

g << f<<2>> >>

NOTE: for the moment we assume that node static arguments don't appear in types.
-}

data StaticEnv = StaticEnv
  { sConsts :: Map OrigName Expression
  , sTypes  :: Map OrigName Type
  }

sEmpty :: StaticEnv
sEmpty = StaticEnv { sConsts = Map.empty, sTypes = Map.empty }

sType :: Ident -> Type -> StaticEnv
sType x t = sEmpty { sTypes = Map.singleton (identOrigName x) t }

sConst :: Ident -> Expression -> StaticEnv
sConst x e = sEmpty { sConsts = Map.singleton (identOrigName x) e }

sJoin :: [StaticEnv] -> StaticEnv
sJoin envs = StaticEnv { sConsts = Map.unions (map sConsts envs)
                       , sTypes = Map.unions (map sTypes envs)
                       }

--------------------------------------------------------------------------------

instantiateProfile :: StaticEnv -> NodeProfile -> NodeProfile
instantiateProfile env prof =
  NodeProfile
    { nodeInputs  = map (instantiateInputBinder env) (nodeInputs prof)
    , nodeOutputs = map (instantiateBinder env)      (nodeOutputs prof)
    }

instantiateInputBinder :: StaticEnv -> InputBinder -> InputBinder
instantiateInputBinder env inp =
  case inp of
    InputConst x t -> InputConst x (instantiateType env t)
    InputBinder b  -> InputBinder (instantiateBinder env b)

instantiateBinder :: StaticEnv -> Binder -> Binder
instantiateBinder env b =
  b { binderType  = iType (binderType b)
    , binderClock = iClock <$> binderClock b }
  where
  iClock (WhenClock r e i) = WhenClock r (iConst e) i
  iConst = instantiateConst env
  iType  = instantiateType env


-- | Instantiate a type with the given static parameters.
instantiateType :: StaticEnv -> Type -> Type
instantiateType env ty
  | Map.null (sConsts env) && Map.null (sTypes env) = ty -- a very common case
  | otherwise =
    case ty of
      ArrayType t e     -> ArrayType (iType t) (iConst e)
      NamedType x       -> Map.findWithDefault ty (nameOrigName x) (sTypes env)
      TypeRange r t     -> TypeRange r (iType t)
      IntSubrange e1 e2 -> IntSubrange (iConst e1) (iConst e2)
      IntType           -> ty
      RealType          -> ty
      BoolType          -> ty
      TVar {}           -> ty
  where
  iType  = instantiateType env
  iConst = instantiateConst env


-- | Instantiate a constant with the given static parameters.
-- These are just constants that can appear in types, so pretty much
-- an expression denoting an `int`.  However, to support selectors and functions
-- we pretty much do all but the temporal constructs.
instantiateConst :: StaticEnv -> Expression -> Expression
instantiateConst env expr
  | Map.null (sConsts env) && Map.null (sTypes env) = expr -- a very common case
  | otherwise =
    case expr of
      ERange r e -> ERange r (iConst e)
      Var x -> Map.findWithDefault expr (nameOrigName x) (sConsts env)
      Lit {} -> expr

      Select e s -> Select (iConst e) (iSelect s)
      Tuple es -> Tuple (map iConst es)
      Array es -> Array (map iConst es)
      Struct s fs -> Struct (iStructTy s) (map iField fs)
      UpdateStruct s e fs ->
        UpdateStruct (iStructTy s) (iConst e) (map iField fs)

      WithThenElse e1 e2 e3 -> WithThenElse (iConst e1) (iConst e2) (iConst e3)
      Call (NodeInst n as) es Nothing ->
        Call (NodeInst n (map iArg as)) (map iConst es) Nothing
      Call {}       -> bad "call with a clock"

      When {}       -> bad "WhenClock"
      Merge {}      -> bad "Merge"

  where
  bad x = panic "instantiateConst" [ "Unexpected construct: " ++ x ]

  iStructTy x = toNameTy (iType (NamedType x))
  toNameTy ty = case ty of
                  TypeRange _ t -> toNameTy t
                  NamedType t   -> t
                  _             -> bad "Struct type was not a named type?"

  iConst = instantiateConst env
  iType  = instantiateType env
  iSelect sel =
    case sel of
      SelectField {}  -> sel
      SelectElement e -> SelectElement (iConst e)
      SelectSlice s   -> SelectSlice (iSlice s)
  iSlice sl = ArraySlice { arrayStart = iConst (arrayStart sl)
                         , arrayEnd   = iConst (arrayEnd sl)
                         , arrayStep  = iConst <$> arrayStep sl
                         }

  iField f = f { fValue = iConst (fValue f) }
  iArg arg = case arg of
               TypeArg t -> TypeArg (iType t)
               ExprArg e -> ExprArg (iConst e)
               NodeArg t ni -> NodeArg t (iInst ni)
               ArgRange r s -> ArgRange r (iArg s)
  iInst (NodeInst f as) = NodeInst f (map iArg as)



checkSafetyType :: NodeInfo -> Safety -> NodeType -> M ()
checkSafetyType ni safe fun =
  do case (safe, niSafety ni) of
       (Safe, Unsafe) ->
          reportError ("Invalid unsafe node parameter" <+> fDoc)
       _ -> pure ()
     case (fun, niType ni) of
       (Function, Node) ->
          reportError ("Expected a function parameter, but"
                                                      <+> fDoc <+> "is a node.")
       _ -> pure ()
  where
  fDoc = backticks (pp (niName ni))


checkEnoughStaticArgs :: NodeInfo -> [StaticArg] -> M ()
checkEnoughStaticArgs ni as =
  case compare have need of
    EQ -> pure ()
    LT -> reportError
            ("Not enough static arguments in call to"
                <+> backticks (pp (niName ni)))
    GT -> reportError $
            ("Too many static arguments in call to"
                <+> backticks (pp (niName ni)))
  where
  have = length as
  need = length (niStaticParams ni)



checkNodeBody :: NodeBody -> M NodeBody
checkNodeBody nb = addLocals (nodeLocals nb)
  where
  -- XXX: after checking that equations are OK individually,
  -- we should check that the LHS define proper values
  -- (e.g., no missing parts of structs/arrays etc, no repeated declarations)
  -- (NOTE2: although, with partial specifications, some of that might be OK?)
  -- XXX: we also need to check that all outputs were defined.
  --      (although partial specs are also OK sometimes?)
  -- XXX: also check that that all locals have definitions
  --      (again, partial specs ok?)
  -- XXX: also, we should check that equations don't use values
  -- that are not yet defined (e.g., x = x, not OK, but x = pre x is OK)
  addLocals ls =
    case ls of
      []       -> do es <- mapM checkEquation (nodeEqns nb)
                     pure NodeBody { nodeLocals = [], nodeEqns = es }
      l : more ->
          do (d,n) <- checkLocalDecl l (addLocals more)
             pure n { nodeLocals = d : nodeLocals n }

checkLocalDecl :: LocalDecl -> M a -> M (LocalDecl,a)
checkLocalDecl ld m =
  case ld of
    LocalVar b   -> apFstM LocalVar  (checkBinder b m)
    LocalConst c -> apFstM LocalConst (checkConstDef c m)


checkConstDef :: ConstDef -> M a -> M (ConstDef, a)
checkConstDef c m =
  do (c1,t) <- checkDef
     addFst c1 (withConst (constName c) t m)
  where
  checkDef =
    inRange (range (constName c)) $
    case constDef c of
      Nothing ->
        case constType c of
          Nothing -> reportError $ nestedError
                     "Constant declaration with no type or default."
                     [ "Name:" <+> pp (constName c) ]
          Just t -> do t1 <- checkType t
                       pure (c { constType = Just t }, t1)

      Just e ->
        do t <- case constType c of
                  Nothing -> newTVar
                  Just t  -> checkType t
           e1 <- checkConstExpr e t
           pure (c { constType = Just t, constDef = Just e1 }, t)

checkInputBinder :: InputBinder -> M a -> M (InputBinder, a)
checkInputBinder ib m =
  case ib of
    InputBinder b -> apFstM InputBinder (checkBinder b m)
    InputConst i t ->
      do t1 <- checkType t
         addFst (InputConst i t1) (withConst i t1 m)

checkBinder :: Binder -> M a -> M (Binder,a)
checkBinder b m =
  do (c1,c) <-
        case binderClock b of
          Nothing -> pure (Nothing,BaseClock)
          Just e  -> do (e',_c) <- checkClockExpr e
                        pure (Just e', KnownClock e')
     t <- checkType (binderType b)
     let ty   = CType { cType = t, cClock = c }
         newB = b { binderType = t, binderClock = c1 }
     addFst newB $ withLocal (binderDefines b) ty m

checkInputBinders :: [InputBinder] -> M a -> M ([InputBinder],a)
checkInputBinders = checkNested checkInputBinder

checkOutputBinders :: [Binder] -> M a -> M ([Binder],a)
checkOutputBinders = checkNested checkBinder

addFst :: a -> M b -> M (a,b)
addFst a m =
  do b <- m
     pure (a,b)

apFstM :: (a -> x) -> M (a,b) -> M (x,b)
apFstM f m =
  do (a,b) <- m
     pure (f a, b)

checkNested :: (forall a. t -> M a -> M (t,a)) -> [t] -> M b -> M ([t],b)
checkNested work things m =
  case things of

    [] ->
      do a <- m
         pure ([],a)

    t : ts ->
      do (t1,(ts1,a)) <- work t (checkNested work ts m)
         pure (t1:ts1,a)




checkType :: Type -> M Type
checkType ty =
  case ty of
    TypeRange r t -> inRange r (checkType t)
    IntType       -> pure IntType
    BoolType      -> pure BoolType
    RealType      -> pure RealType
    TVar x        -> panic "checkType" [ "Unexpected type variable:"
                                       , "*** Tvar: " ++ showPP x ]
    IntSubrange x y ->
      do a <- checkConstExpr x IntType
         b <- checkConstExpr y IntType
         leqConsts x y
         pure (IntSubrange a b)
    NamedType x ->
      do _t <- resolveNamed x
         pure ty -- or the resolved type?
    ArrayType t n ->
      do n1 <- checkConstExpr n IntType
         leqConsts (Lit (Int 0)) n
         t1 <- checkType t
         pure (ArrayType t1 n1)


checkEquation :: Equation -> M Equation
checkEquation eqn =
  enterRange $
  case eqn of
    Assert l e ->
        Assert l <$> checkExpr1 e CType { cType = BoolType, cClock = BaseClock }

    Property l e ->
      Property l <$> checkExpr1 e CType { cType = BoolType, cClock = BaseClock }

    IsMain _ -> pure eqn

    IVC _ -> pure eqn -- XXX: what should we check here?

    Define ls e ->
      do (ls1,lts) <- unzip <$> mapM checkLHS ls
         es1 <- checkExpr e lts
         pure (Define ls1 es1)

  where
  enterRange = case eqnRangeMaybe eqn of
                 Nothing -> id
                 Just r  -> inRange r


checkLHS :: LHS Expression -> M (LHS Expression, CType)
checkLHS lhs =
  case lhs of
    LVar i -> do (j,t) <- checkLocalVar i
                 pure (LVar j, t)
    LSelect l s ->
      do (l1,t)  <- checkLHS l
         (s1,t1) <- inferSelector s (cType t)
         pure (LSelect l1 s1, t { cType = t1 })




-- | Infer the type of a constant expression.
-- XXX: Perhaps we can eliminate this function by just using `checkExpr`
-- but disable temporal operators.... We'd have to do something about the
-- clock (perhaps use the base clock?), and also we'd have to treat local
-- variables (parameters or locals) as temporal constructs.
checkConstExpr :: Expression -> Type -> M Expression
checkConstExpr expr ty =
  case expr of
    ERange r e -> inRange r (checkConstExpr e ty)
    Var x      -> checkConstVar x ty
    Lit l      -> do ensure (Subtype (inferLit l) ty)
                     pure (Lit l)
    When {}    -> reportError "`when` is not a constant expression."
    Tuple {}   -> reportError "tuples cannot be used in constant expressions."
    Array es   ->
      do elT <- newTVar
         es1 <- mapM (`checkConstExpr` elT) es
         let n = Lit $ Int $ fromIntegral $ length es
         ensure (Subtype (ArrayType elT n) ty)
         pure (Array es1)

    Struct s fs -> checkStruct s fs ty checkConstExpr

    UpdateStruct s e fs -> checkStructUpdate s e fs ty checkConstExpr

    Select e s ->
      do t <- newTVar
         e1 <- checkConstExpr e t
         (s1,t1) <- inferSelector s t
         ensure (Subtype t1 ty)
         pure (Select e1 s1)

    WithThenElse e1 e2 e3 ->
      WithThenElse <$> checkConstExpr e1 BoolType
                   <*> checkConstExpr e2 ty
                   <*> checkConstExpr e3 ty

    Merge {}   -> reportError "`merge` is not a constant expression."
    Call {}   -> reportError "constant expressions do not support calls."

-- | Check that the expression has the given type.
checkExpr1 :: Expression -> CType -> M Expression
checkExpr1 e t = checkExpr e [t]




{- | Check if an expression has the given type.
Tuples and function calls may return multiple results,
which is why we provide multiple clocked types. -}
checkExpr :: Expression -> [CType] -> M Expression
checkExpr expr tys =
  case expr of
    ERange r e -> inRange r (checkExpr e tys)

    Var x ->
      inRange (range x) $
        do ty <- one tys
           checkVar x ty

    Lit l ->
      do ty <- one tys
         let lt = inferLit l
         ensure (Subtype lt (cType ty))
         pure (Lit l)

    e `When` c ->
      do checkTemporalOk "when"
         (c1,cl) <- checkClockExpr c -- `cl` is the clock of c

         tys1 <- for tys $ \ty ->
                   do sameClock (cClock ty) (KnownClock c)
                      pure ty { cClock = cl }

         e1 <- checkExpr e tys1
         pure (e1 `When` c1)

    Tuple es
      | have == need -> Tuple <$> zipWithM checkExpr1 es tys
      | otherwise    -> reportError $ nestedError "Arity mismatch in tuple"
                          [ "Expected arity:" <+> text (show need)
                          , "Actual arity:" <+> text (show have) ]
      where have = length es
            need = length tys

    Array es ->
      do ty  <- one tys
         elT <- newTVar
         let n = Lit $ Int $ fromIntegral $ length es
         ensure (Subtype (ArrayType elT n) (cType ty))
         let elCT = ty { cType = elT }
         es1 <- mapM (`checkExpr1` elCT) es
         pure (Array es1)

    Select e s ->
      do ty        <- one tys
         recT      <- newTVar
         e1        <- checkExpr1 e ty { cType = recT }
         (s1,t1)   <- inferSelector s recT
         ensure (Subtype t1 (cType ty))
         pure (Select e1 s1)

    Struct s fs ->
      do ty <- one tys
         checkStruct s fs (cType ty) $ \e t ->
           checkExpr1 e ty { cType = t }

    UpdateStruct s e fs ->
      do ty <- one tys
         checkStructUpdate s e fs (cType ty) $ \ex t ->
            checkExpr1 ex ty { cType = t }

    WithThenElse e1 e2 e3 ->
      WithThenElse <$> checkConstExpr e1 BoolType
                   <*> checkExpr e2 tys
                   <*> checkExpr e3 tys

    Merge i as ->
      do (j,t) <- checkLocalVar i
         mapM_ (sameClock (cClock t) . cClock) tys
         let it      = cType t
             ts      = map cType tys
             check c = checkMergeCase j c it ts
         as1 <- mapM check as
         pure (Merge j as1)

    Call (NodeInst call as) es cl

      -- Special case for @^@ because its second argument is a constant
      -- expression, not an ordinary one.
      | CallPrim r (Op2 Replicate) <- call ->
        inRange r $
        do notClocked
           unless (null as) $ reportError "`^` does not take static arguments."
           case es of
             [e1,e2] ->
               do ty <- one tys
                  e2' <- checkConstExpr e2 IntType
                  elT <- newTVar
                  e1' <- checkExpr e1 [ty { cType = elT }]
                  ensure (Subtype (ArrayType elT e2) (cType ty))
                  pure (eOp2 r Replicate e1' e2')
             _ -> reportError $ text (showPP call ++ " expexts 2 arguments.")

      | otherwise ->
        case call of
          CallUser f      -> checkCall f as es cl tys
          CallPrim r prim -> notClocked >> checkPrim r prim as es tys

      where notClocked =
              case cl of
                Nothing -> pure ()
                Just _  -> reportError "Unexpected clock annotation in call"

-- | Assert that a given expression has only one type (i.e., is not a tuple)
one :: [CType] -> M CType
one xs =
  case xs of
    [x] -> pure x
    _   -> reportError $
           nestedError "Arity mismatch."
             [ "Expected arity:" <+> int (length xs)
             , "Actual arity:" <+> "1"
             ]


checkStructType :: Name -> M (Name, [FieldType])
checkStructType s =
  do ty   <- checkType (NamedType s)
     let name = case ty of
                  NamedType nm -> nm
                  _ -> panic "checkStructType"
                         [ "Unexpected struct type ellaboration:"
                         , "*** Struct type: " ++ showPP s
                         , "*** Result: " ++ showPP ty
                         ]
     fs <- lookupStruct name
     pure (name,fs)


-- | Check an struct expression. Also fills in defaults for missing fields.
checkStruct :: Name -> [Field Expression] -> Type ->
               (Expression -> Type -> M Expression) ->
               M Expression
checkStruct s fs expected checkF =
  do (actualName, fieldTs) <- checkStructType s
     ensure (Subtype (NamedType actualName) expected)
     distinctFields fs

     let fieldMap = Map.fromList [ (fName f, f) | f <- fs ]

     fs1 <- for fieldTs $ \ft ->
              case Map.lookup (fieldName ft) fieldMap of

                Nothing -> -- Field not initialized
                  case fieldDefault ft of
                    Nothing -> reportError $
                      "Field" <+> backticks (pp (fieldName ft)) <+>
                      "of"    <+> backticks (pp actualName)     <+>
                      "is not initialized."
                    Just e1 -> pure Field { fName  = fieldName ft
                                          , fValue = e1
                                          }

                Just f -> -- Field initialized
                  do e1 <- checkF (fValue f) (fieldType ft)
                     pure f { fValue = e1 }

     pure (Struct actualName fs1)

-- | Check a structure updatating expression.
checkStructUpdate ::
  Name -> Expression -> [Field Expression] -> Type ->
  (Expression -> Type -> M Expression) ->
  M Expression
checkStructUpdate s e fs expect checkF =
  do (actualName, fieldTs) <- checkStructType s
     e1 <- checkF e expect
     distinctFields fs
     fs1 <- for fs $ \f ->
              case find ((fName f ==) . fieldName) fieldTs of
                Just ft ->
                  do fe <- checkF (fValue f) (fieldType ft)
                     pure f { fValue = fe }
                Nothing -> reportError $
                  "Struct"                <+> backticks (pp actualName) <+>
                  "does not have a field" <+> backticks (pp (fName f))
     pure (UpdateStruct actualName e1 fs1)

-- | Check that all of the fields are different.
distinctFields :: [Field Expression] -> M ()
distinctFields = mapM_ check . group . sort . map fName
  where
  check g =
    case g of
      []    -> panic "distinctFields" ["`group` returned an empty list?"]
      [_]   -> pure ()
      f : _ -> reportError $ nestedError
                ("Repeated occurances of field" <+> backticks (pp f))
                (map (pp . range) g)



-- | Check the type of a call to a user-defined node.
checkCall :: Name ->
             [StaticArg] ->
             [Expression] ->
             Maybe ClockExpr ->
             [CType] ->
             M Expression
checkCall f as es0 cl0 tys =
  do reqSafety <- getUnsafeLevel
     reqTemporal <- getTemporalLevel
     cl <- case cl0 of
             Nothing -> pure Nothing
             Just c  -> case reqTemporal of
                          Node -> Just . fst <$> checkClockExpr c
                          Function ->
                            reportError $ nestedError
                               "Invalid clocked call"
                               [ "Expected to be inside a node."
                               , "We are inside a function."
                               ]

     (ni,prof) <- prepUserNodeInst f as reqSafety reqTemporal
     (es1,mp) <- checkInputs cl [] Map.empty (nodeInputs prof) es0
     checkOuts cl mp (nodeOutputs prof)
     pure (Call ni es1 cl)
  where
  renBinderClock cl mp b =
    case binderClock b of
      Nothing -> pure $ case cl of
                          Nothing -> BaseClock
                          Just c  -> KnownClock c
      Just (WhenClock r p i) ->
        case cl of
          Just _ ->
            reportError $ nestedError
              "Unsupported: nested clocks in call"
              [ "Please let us know, if you'd find this useful." ]

          Nothing ->
            case Map.lookup i mp of
              Just (Right j)            -> pure (KnownClock (WhenClock r p j))
              Just (Left l) | matches p -> pure BaseClock
                where matches v = case v of
                                    ERange _ v1 -> matches v1
                                    Lit l1 -> l == l1
                                    _ -> False
              _ -> reportError $
                text ("Parameter for clock " ++ show (backticks (pp i)) ++
                 " is not an identifier.")


  checkInputs cl done mp is es =
    case (is,es) of
      ([],[]) -> pure (reverse done,mp)
      (b:bs,c:cs) -> do (e,mp1) <- checkIn cl mp b c
                        checkInputs cl (e:done) mp1 bs cs
      _ -> reportError $ nestedError
               ("Bad arity in call to" <+> pp f)
               [ "Expected:" <+> int (length done + length is)
               , "Actual:" <+> int (length done + length es)
               ]

  checkIn cl mp ib e =
    case ib of
      InputBinder b ->
        do c  <- renBinderClock cl mp b
           e1 <- case c of
                   BaseClock ->
                      checkExpr1 e CType { cClock = c, cType = binderType b }
                   KnownClock c1 ->
                      checkExpr1 (e `When` c1)
                            CType { cClock = c, cType = binderType b }
                   ClockVar _ -> panic "checkIn" [ "Unexpectd clock var." ]
           pure ( e1
                , case isClock e of
                    Just k  -> Map.insert (binderDefines b) k mp
                    Nothing -> mp
                )
      InputConst _ t ->
        do e1 <- checkConstExpr e t
           pure (e1,mp)

  isClock e =
    case e of
      ERange _ e1    -> isClock e1
      Var (Unqual i) -> Just (Right i)
      Lit l          -> Just (Left l)
      _              -> Nothing

  checkOuts cl mp bs
    | have == need = zipWithM_ (checkOut cl mp) bs tys
    | otherwise = reportError $ nestedError
                  "Arity mistmatch in function call."
                  [ "Function:" <+> pp f
                  , "Returns:" <+> text (show have) <+> "restuls"
                  , "Expected:" <+> text (show need) <+> "restuls" ]
      where have = length bs
            need = length tys


  checkOut cl mp b ty =
    do let t = binderType b
       c <- renBinderClock cl mp b
       subCType CType { cClock = c, cType = t } ty


-- | Infer the type of a call to a primitive node.
checkPrim :: SourceRange -> PrimNode -> [StaticArg] -> [Expression] ->
              [CType] -> M Expression
checkPrim r prim as es tys =
  case prim of

    Iter {} -> notYetImplemented "iterators."

    Op1 op ->
      case es of
        [e] -> noStatic op >> checkOp1 r op e tys
        _   -> reportError (pp op <+> "expects 1 argument.")

    Op2 op ->
      case es of
        [e1,e2] -> noStatic op >> checkOp2 r op e1 e2 tys
        _ -> reportError (pp op <+> "expects 2 arguments.")

    ITE ->
      case es of
        [e1,e2,e3] ->
          do noStatic ITE
             c <- case tys of
                    []     -> newClockVar -- XXX: or report error?
                    t : ts -> do let c = cClock t
                                 mapM_ (sameClock c . cClock) ts
                                 pure c
             e1' <- checkExpr1 e1 CType { cClock = c, cType = BoolType }
             e2' <- checkExpr e2 tys
             e3' <- checkExpr e3 tys
             pure (eITE r e1' e2' e3')

        _ -> reportError "`if-then-else` expects 3 arguments."


    OpN op -> noStatic op >> checkOpN r op es tys
  where
  noStatic op =
    unless (null as) $
    reportError (backticks (pp op) <+> "does not take static arguments")


-- | Infer the type for a branch of a merge.
checkMergeCase ::
  Ident -> MergeCase Expression -> Type -> [Type] -> M (MergeCase Expression)
checkMergeCase i (MergeCase p e) it ts =
  do p1 <- checkConstExpr p it
     let clk       = KnownClock (WhenClock (range p1) p1 i)
         toCType t = CType { cClock = clk, cType = t }
     e1 <- checkExpr e (map toCType ts)
     pure (MergeCase p1 e1)



checkCurrent :: Expression -> [CType] -> M Expression
checkCurrent e tys =
  do checkTemporalOk "current"
     tys1 <- for tys $ \ty ->
                do c <- newClockVar
                   pure ty { cClock = c }
     e1 <- checkExpr e tys1

     -- By now we should have figured out the missing clock,
     -- so check straight away
     let checkClock ty newTy =
            sameClock (cClock ty) =<< clockParent (cClock newTy)
     zipWithM_ checkClock tys tys1
     pure e1



-- | Types of unary operators.
checkOp1 :: SourceRange -> Op1 -> Expression -> [CType] -> M Expression
checkOp1 r op e tys =
  do a <- check
     pure (eOp1 r op a)

  where
  check =
    case op of
      Pre ->
        do checkTemporalOk "pre"
           checkExpr e tys

      Current -> checkCurrent e tys

      Not ->
        do ty <- one tys
           e1 <- checkExpr1 e ty { cType = BoolType }
           ensure (Subtype BoolType (cType ty))
           pure e1

      Neg ->
        do ty <- one tys
           t  <- newTVar
           e1 <- checkExpr1 e ty { cType = t }
           ensure (Arith1 "-" t (cType ty))
           pure e1

      IntCast ->
        do ty <- one tys
           e1 <- checkExpr1 e ty { cType = RealType }
           ensure (Subtype IntType (cType ty))
           pure e1

      FloorCast ->
        do ty <- one tys
           e1 <- checkExpr1 e ty { cType = RealType }
           ensure (Subtype IntType (cType ty))
           pure e1

      RealCast ->
        do ty <- one tys
           e1 <- checkExpr1 e ty { cType = IntType }
           ensure (Subtype RealType (cType ty))
           pure e1



-- | Types of binary operators.
checkOp2 ::
  SourceRange -> Op2 -> Expression -> Expression -> [CType] -> M Expression
checkOp2 r op2 e1 e2 tys =
  do (a,b) <- check
     pure (eOp2 r op2 a b)

  where
  check =
    case op2 of
      FbyArr ->
        do checkTemporalOk "->"
           a <- checkExpr e1 tys
           b <- checkExpr e2 tys
           pure (a,b)

      Fby ->
       do checkTemporalOk "fby"
          a <- checkExpr e1 tys
          b <- checkExpr e2 tys
          pure (a,b)

      CurrentWith ->
        do checkTemporalOk "currentWith"
           a <- checkExpr    e1 tys
           b <- checkCurrent e2 tys
           pure (a,b)

      And      -> bool2
      Or       -> bool2
      Xor      -> bool2
      Implies  -> bool2

      Eq       -> eqRel "="
      Neq      -> eqRel "<>"

      Lt       -> ordRel "<"
      Leq      -> ordRel "<="
      Gt       -> ordRel ">"
      Geq      -> ordRel ">="

      Add      -> arith "+"
      Sub      -> arith "-"
      Mul      -> arith "*"
      Div      -> arith "/"
      Mod      -> arith "mod"

      Power    -> notYetImplemented "Exponentiation"

      Replicate -> panic "checkOp2" [ "`replicate` should have been checked."]

      Concat -> checkConcat

  bool2     = do ty <- one tys
                 a <- checkExpr1 e1 ty { cType = BoolType }
                 b <- checkExpr1 e2 ty { cType = BoolType }
                 ensure (Subtype BoolType (cType ty))
                 pure (a,b)

  infer2    = do ty <- one tys
                 t1 <- newTVar
                 a <- checkExpr1 e1 ty { cType = t1 }
                 t2 <- newTVar
                 b <- checkExpr1 e2 ty { cType = t2 }
                 pure (a,b,t1,t2,ty)

  ordRel op = do (a,b,t1,t2,ty) <- infer2
                 ensure (CmpOrd op t1 t2)
                 ensure (Subtype BoolType (cType ty))
                 pure (a,b)

  arith x   = do (a,b,t1,t2,ty) <- infer2
                 ensure (Arith2 x t1 t2 (cType ty))
                 pure (a,b)

  eqRel op  = do ty   <- one tys
                 n    <- exprArity e1
                 tv1s <- replicateM n newTVar
                 tv2s <- replicateM n newTVar
                 let toTy t = ty { cType = t }
                 a <- checkExpr e1 (map toTy tv1s)
                 b <- checkExpr e2 (map toTy tv2s)
                 zipWithM_ (\t1 t2 -> ensure (CmpEq op t1 t2)) tv1s tv2s
                 ensure (Subtype BoolType (cType ty))
                 pure (a,b)

  checkConcat =
    do ty <- one tys
       a0 <- newTVar
       e1' <- checkExpr1 e1 ty { cType = a0 }
       b0 <- newTVar
       e2' <- checkExpr1 e2 ty { cType = b0 }
       a <- tidyType a0
       b <- tidyType b0
       case a of
         ArrayType elT1 sz1 ->
           case b of
             ArrayType elT2 sz2 ->
               do c <- newTVar
                  ensure (Subtype elT1 c)
                  ensure (Subtype elT2 c)
                  sz <- addExprs sz1 sz2
                  ensure (Subtype (ArrayType c sz) (cType ty))
                  pure (e1',e2')
             TVar {} -> noInfer "right"
             _       -> typeError "right" b
         TVar {} ->
           case b of
             ArrayType {} -> noInfer "left"
             TVar {}      -> noInfer "left"
             _            -> typeError "left" a
         _ -> typeError "left" a

    where
    noInfer x = reportError ("Failed to infer the type of the" <+> x <+>
                                                          "argument of `|`")

    typeError x t = reportError $ nestedError
                      ("Incorrect" <+> x <+> "argument to `|`")
                      [ "Expected:" <+> "array"
                      , "Actual type:" <+> pp t ]


-- | Check a variable arity operator.
checkOpN :: SourceRange -> OpN -> [Expression] -> [CType] -> M Expression
checkOpN r op es tys =
  case op of
    AtMostOne -> boolOp
    Nor       -> boolOp
  where
  boolOp =
    do ty <- one tys
       let bool = ty { cType = BoolType }
       es1 <- for es $ \e -> checkExpr1 e bool
       ensure (Subtype BoolType (cType ty))
       pure (eOpN r op es1)



-- | Check the type of a variable.
checkVar :: Name -> CType -> M Expression
checkVar x ty =
  case x of
    Unqual i ->
      case rnThing (nameOrigName x) of
        AVal   -> do (j,c) <- checkLocalVar i
                     subCType c ty
                     pure (Var (Unqual j))
        AConst -> checkConstVar x (cType ty)
        t -> panic "checkVar" [ "Identifier is not a value or a constnat:"
                              , "*** Name: " ++ showPP x
                              , "*** Thing: " ++ showPP t ]

    Qual {}  -> panic "checkVar" [ "Unexpected qualified name"
                                 , "*** Name: " ++ showPP x ]



-- | Check the type of a named constnat.
checkConstVar :: Name -> Type -> M Expression
checkConstVar x ty = inRange (range x) $
                     do t1 <- lookupConst x
                        ensure (Subtype t1 ty)
                        pure (Var x)

-- | Check a local variable. Returns the elaborated variable and its type.
checkLocalVar :: Ident -> M (Ident, CType)
checkLocalVar i =
  do ct <- lookupLocal i
     pure (i,ct) -- XXX: elaborate



-- | Infer the type of a literal.
inferLit :: Literal -> Type
inferLit lit =
     case lit of
       Int _   -> IntSubrange (Lit lit) (Lit lit)
       Real _  -> RealType
       Bool _  -> BoolType

-- | Check a clock expression.
-- Returns the elaborated clock expression, and its clock.
checkClockExpr :: ClockExpr -> M (ClockExpr,IClock)
checkClockExpr (WhenClock r v i) =
  inRange r $
    do (j,ct) <- checkLocalVar i
       w      <- checkConstExpr v (cType ct)
       pure (WhenClock r w j, cClock ct)

--------------------------------------------------------------------------------

inferSelector :: Selector Expression -> Type -> M (Selector Expression, Type)
inferSelector sel ty0 =
  do ty <- tidyType ty0
     case sel of
       SelectField f ->
         case ty of
           NamedType a ->
             do fs <- lookupStruct a
                case find ((f ==) . fieldName) fs of
                  Just fi  -> pure (sel,fieldType fi)
                  Nothing ->
                    reportError $
                    nestedError
                    "Struct has no such field:"
                      [ "Struct:" <+> pp a
                      , "Field:" <+> pp f ]

           TVar {} -> notYetImplemented "Record selection from unknown type"

           _ -> reportError $
                nestedError
                  "Argument to struct selector is not a struct:"
                  [ "Selector:" <+> pp sel
                  , "Input:" <+> pp ty0
                  ]

       SelectElement n ->
         case ty of
           ArrayType t _sz ->
             do n1 <- checkConstExpr n IntType
                -- XXX: check that 0 <= && n < sz ?
                pure (SelectElement n1, t)

           TVar {} -> notYetImplemented "Array selection from unknown type"

           _ -> reportError $
                nestedError
               "Argument to array selector is not an array:"
                [ "Selector:" <+> pp sel
                , "Input:" <+> pp ty0
                ]

       SelectSlice _s ->
        case ty of
          ArrayType _t _sz -> notYetImplemented "array slices"
          TVar {} -> notYetImplemented "array slice on unknown type."
          _ -> reportError $
               nestedError
               "Arrgument to array slice is not an array:"
               [ "Selector:" <+> pp sel
               , "Input:" <+> pp ty0
               ]





--------------------------------------------------------------------------------
-- Comparsions of types

subCType :: CType -> CType -> M ()
subCType x y =
  do ensure (Subtype (cType x) (cType y))
     sameClock (cClock x) (cClock y)








--------------------------------------------------------------------------------
-- Clocks


-- | Are these the same clock.  If so, return the one that is NOT a 'ConstExpr'
-- (if any).
sameClock :: IClock -> IClock -> M ()
sameClock x0 y0 =
  do x <- zonkClock x0
     y <- zonkClock y0
     case (x,y) of
       (ClockVar a, _) -> bindClockVar a y
       (_, ClockVar a) -> bindClockVar a x
       (BaseClock,BaseClock) -> pure ()
       (KnownClock a, KnownClock b) -> sameKnownClock a b
       _ -> reportError $ nestedError
             "The given clocks are different:"
             [ "Clock 1:" <+> pp x
             , "Clock 2:" <+> pp y
             ]

-- | Is this the same known clock.
sameKnownClock :: ClockExpr -> ClockExpr -> M ()
sameKnownClock c1@(WhenClock _ e1_init i1) c2@(WhenClock _ e2_init i2) =
  do unless (i1 == i2) $
        reportError $
        nestedError
          "The given clocks are different:"
          [ "Clock 1:" <+> pp c1
          , "Clock 2:" <+> pp c2
          ]
     sameConsts e1_init e2_init

-- | Get the clock of a clock, or fail if we are the base clock.
clockParent :: IClock -> M IClock
clockParent ct0 =
  do ct <- zonkClock ct0
     case ct of
       BaseClock -> reportError "The base clock has no parent."
       KnownClock (WhenClock _ _ i) -> cClock <$> lookupLocal i
                                          -- XXX: This can be a constnat?
       ClockVar _ -> reportError "Failed to infer the expressions's clock"



--------------------------------------------------------------------------------
-- Expressions

binConst :: (Integer -> Integer -> Integer) ->
            Expression -> Expression -> M Expression
binConst f e1 e2 =
  do x <- intConst e1
     y <- intConst e2
     pure $ Lit $ Int $ f x y

addExprs :: Expression -> Expression -> M Expression
addExprs = binConst (+) -- XXX: Can make an expression instead

minExprs :: Expression -> Expression -> M Expression
minExprs = binConst min

maxConsts :: Expression -> Expression -> M Expression
maxConsts = binConst max








