{-# Language OverloadedStrings, Rank2Types #-}
module Language.Lustre.TypeCheck where

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (find,transpose)
import Control.Monad(when,unless,zipWithM_,zipWithM,foldM)
import Text.PrettyPrint as PP
import Data.List(group,sort)
import Data.Traversable(for)
import Data.Foldable(for_)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic
import Language.Lustre.Monad(LustreM)
import Language.Lustre.TypeCheck.Monad
import Language.Lustre.TypeCheck.Constraint
import Language.Lustre.TypeCheck.Prims
import Language.Lustre.TypeCheck.Utils


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
             Just e  -> do e' <- checkConstExpr e t
                           pure (Just e')
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
    inClockScope $
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
          do e' <- checkConstExpr e t
             pure (ExprArg e', sConst x e')
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
      (InputConst _ t, InputConst _ t1) -> subType t1 t
      (InputBinder b, InputBinder b1) -> subCType (cTypeOf b1) (cTypeOf b)
      (InputBinder {}, InputConst {}) ->
        reportError "Expected a constant input."
      (InputConst {}, InputBinder {}) ->
        reportError "Unexpected constant input." -- XXX: perhaps this is ok?

  checkOut arg param = subCType (cTypeOf arg) (cTypeOf param)

  subCType x y =
    do subType (cType x) (cType y)
       sameClock (cClock x) (cClock y)



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
  where
  iType  = instantiateType env
  iConst = instantiateConst env


{- | Instantiate a constant with the given static parameters.
These are just constants that can appear in types, so pretty much
an expression denoting an `int`.  However, to support selectors and functions
we pretty much do all but the temporal constructs. -}
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
        UpdateStruct (iStructTy <$> s) (iConst e) (map iField fs)

      WithThenElse e1 e2 e3 -> WithThenElse (iConst e1) (iConst e2) (iConst e3)
      Call (NodeInst n as) es Nothing ->
        Call (NodeInst n (map iArg as)) (map iConst es) Nothing
      Call {}       -> bad "call with a clock"

      When {}       -> bad "WhenClock"
      Merge {}      -> bad "Merge"
      Const {}      -> panic "instantiateConst" [ "Unexpected `Const`" ]

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
  {- NOTE: there are all kinds of things that one could check here, if
  we intentd to run the Lustre program.  For example, all variables should
  have definitions, and maybe we don't want recursive equations.
  However, when using Lustre as a front-end to a model checker, it is sometimes
  conveninet to relax such issues.  In that case we think of the equations
  more in their math form: not so much LHS is defined by RHS, but rather
  we'd just like them to be equal.  With that mind set it makes sense to
  allow partial specifications, and even recursive ones:  the result may
  be that we transition to multiple next states (i.e., we are no longer
  deterministic), or perhaps we get stuck (e.g., if a recursive equation
  has no fixed point).
  -}

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
        do (e',t) <- case constType c of
                       Nothing -> inferConstExpr e
                       Just t  -> do t' <- checkType t
                                     e' <- checkConstExpr e t'
                                     pure (e',t')
           pure (c { constType = Just t, constDef = Just e' }, t)

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
          Just e  -> do (e',_) <- inferClockExpr e
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

--------------------------------------------------------------------------------


-- | Validate a type.
checkType :: Type -> M Type
checkType ty =
  case ty of
    TypeRange r t -> inRange r (checkType t)
    IntType       -> pure IntType
    BoolType      -> pure BoolType
    RealType      -> pure RealType
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
         leqConsts (Lit (Int 0)) n1
         t1 <- checkType t
         pure (ArrayType t1 n1)


-- | Validate an equation.
checkEquation :: Equation -> M Equation
checkEquation eqn =
  enterRange $
  case eqn of
    Assert l e ->
      do (e',_clk) <- checkExpr1 e BoolType
         pure (Assert l e')  -- XXX: Save clock?

    Property l e ->
      do (e',_clk) <- checkExpr1 e BoolType
         pure (Property l e') -- XXX: Save clock?

    IsMain _ -> pure eqn

    IVC _ -> pure eqn -- XXX: what should we check here?

    Define ls e ->
      do (ls',lts) <- unzip <$> mapM inferLHS ls
         (e',cts) <- inferExpr e
         sameLen lts cts
         for_ (zip lts cts) $ \(lt,ct) ->
           do sameClock (cClock lt) (cClock ct)
              subType (cType ct) (cType lt)
         pure (Define ls' e')

  where
  enterRange = case eqnRangeMaybe eqn of
                 Nothing -> id
                 Just r  -> inRange r


-- | Infer the type of the left-hand-side of a declaration.
inferLHS :: LHS Expression -> M (LHS Expression, CType)
inferLHS lhs =
  case lhs of
    LVar i -> do t <- lookupLocal i
                 pure (LVar i, t)
    LSelect l s ->
      do (l1,t)  <- inferLHS l
         (s1,t1) <- inferSelector s (cType t)
         pure (LSelect l1 s1, t { cType = t1 })



{- | Infer the type of an expression.
Tuples and function calls may return multiple results,
which is why we provide multiple clocked types. -}
inferExpr :: Expression -> M (Expression, [CType])
inferExpr expr =
  case expr of
    ERange r e -> inRange r (inferExpr e)

    Var x ->
      inRange (range x) $
        do (e1,ct) <- inferVar x
           pure (e1,[ct])

    Lit l ->
      do let ty = inferLit l
         c <- newClockVar
         let ct = CType { cType = ty, cClock = c }
         pure (Const (Lit l) ct, [ct])

    e `When` c ->
      do checkTemporalOk "when"
         (c',ct1)  <- inferClockExpr c
         (e',ct2s) <- inferExpr e
         cts <- for ct2s $ \ct ->
                  do sameClock (cClock ct) (cClock ct1)
                     pure ct { cClock = KnownClock c' }
         pure (e' `When` c', cts)

    Tuple es ->
      do (es',cts) <- unzip <$> mapM inferExpr1 es
         pure (Tuple es',cts)

    Array es ->
      do (es',cts) <- unzip <$> mapM inferExpr1 es
         let ne = Lit $ Int $ fromIntegral $ length es
             done c t =
               do let ct = CType { cClock = c, cType = ArrayType t ne }
                  pure (Array es', [ct])
         case cts of
           [] -> notYetImplemented "Empty arrays"
           elT : more ->
            do t <- foldM tLUB (cType elT)  (map cType more)
               mapM_ (sameClock (cClock elT)) (map cClock more)
               done (cClock elT) t

    Select e s ->
      do (e',recCT) <- inferExpr1 e
         (s',ty)    <- inferSelector s (cType recCT)
         let ct = recCT { cType = ty }
         pure (Select e' s', [ct])

    Struct s fs ->
      do (e',ct) <- inferStruct s fs
         pure (e',[ct])

    UpdateStruct s e fs ->
      do (e',ct) <- inferStructUpdate s e fs
         pure (e',[ct])

    WithThenElse e1 e2 e3 ->
      do e1'       <- checkConstExpr e1 BoolType
         (e2',ct1) <- inferExpr e2
         (e3',ct2) <- inferExpr e3
         sameLen ct1 ct2
         ct        <- zipWithM ctLUB ct1 ct2
         pure (WithThenElse e1' e2' e3', ct)

    Merge i as ->
      do ctI <- lookupLocal i
         (as',ctss) <- unzip <$> for as (inferMergeCase i (cType ctI))
         case ctss of
           [] -> reportError "Empty merge case"
           ctAlt : alts ->
             do for_ alts (sameLen ctAlt)
                let byCol = transpose (map (map cType) ctss)
                cts <- for byCol $ \ ~(t:ts) ->
                         do t1 <- foldM tLUB t ts
                            pure CType { cClock = cClock ctI, cType = t1 }
                pure (Merge i as',cts)

    Call (NodeInst call as) es cl ->
      case call of
        CallUser f        -> inferCall f as es cl
        CallPrim r prim
          | Nothing <- cl -> inferPrim r prim as es 
          | otherwise     -> reportError "Unexpected clock annotation in call"

    Const {} -> panic "inferExpr" [ "Unexpected `Const` expression." ]


-- | Infer the type of an expression that should not return multiple results.
inferExpr1 :: Expression -> M (Expression,CType)
inferExpr1 e =
  do (e',cts) <- inferExpr e
     ct       <- one cts
     pure (e',ct)

{- | Infer the type of a constant expression.
NOTE: the elaborated result will contain `Const` annotations,
which is a little bogus, but they will go away in the `NoStatic pass. -}
inferConstExpr :: Expression -> M (Expression,Type)
inferConstExpr expr =
  allowTemporal False $
  allowUnsafe   False $
  do (e',ct) <- inferExpr1 expr
     sameClock BaseClock (cClock ct)
     pure (e',cType ct)

-- | Infer the type of a constant expression.
checkConstExpr :: Expression -> Type -> M Expression
checkConstExpr expr ty =
  do (e',t) <- inferConstExpr expr
     subType t ty
     pure e'

checkExpr1 :: Expression -> Type -> M (Expression,IClock)
checkExpr1 e t =
  do (e',ct) <- inferExpr1 e
     subType (cType ct) t
     pure (e', cClock ct)



{- | Ensure that the given named type is a struct.  If so, get the real
name of the struct (e.g., if the original was an alias for a struct),
and alsot its fields, in declaration order. -}
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


-- | Infer the type of a struct formaing expression.
inferStruct :: Name -> [Field Expression] -> M (Expression,CType)
inferStruct s fs =
  do distinctFields fs
     (s',fExpect) <- checkStructType s
     let fieldMap = Map.fromList [ (fName f, f) | f <- fs ]
     i   <- newClockVar
     fs' <- for fExpect $ \ft ->
              case Map.lookup (fieldName ft) fieldMap of

                Nothing -> -- Field not initialized
                  case fieldDefault ft of
                    Nothing -> reportError $
                      "Field" <+> backticks (pp (fieldName ft)) <+>
                      "of"    <+> backticks (pp s')             <+>
                      "is not initialized."
                    Just e1 ->
                      let ct = CType { cType = fieldType ft, cClock = i }
                      in pure Field { fName  = fieldName ft
                                    , fValue = Const e1 ct
                                    }

                Just f -> -- Field initialized
                  do (e,clk) <- checkExpr1 (fValue f) (fieldType ft)
                     sameClock i clk
                     pure f { fValue = e }

     let ct = CType { cClock = i, cType = NamedType s' }
     pure (Struct s' fs', ct)


-- | Infer a structure updatating expression.
inferStructUpdate ::
  Maybe Name -> Expression -> [Field Expression] -> M (Expression,CType)
inferStructUpdate mbS e fs =
  do distinctFields fs
     (e',ct) <- inferExpr1 e
     (actualName, fieldTs) <-
       case mbS of
         Just s -> checkStructType s
         Nothing ->
           do t1 <- tidyType (cType ct)
              case t1 of
                NamedType name ->
                  do fTs <- lookupStruct name
                     pure (name,fTs)
                _ -> reportError $ nestedError
                       "Invalid struct update."
                       [ "Expression is not a struct." ]

     fs' <- for fs $ \f ->
              case find ((fName f ==) . fieldName) fieldTs of

                Just ft ->
                  do (fv,fclk) <- checkExpr1 (fValue f) (fieldType ft)
                     sameClock fclk (cClock ct)
                     pure f { fValue = fv }

                Nothing -> reportError $
                  "Struct"                <+> backticks (pp actualName) <+>
                  "does not have a field" <+> backticks (pp (fName f))

     pure (UpdateStruct (Just actualName) e' fs', ct)



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




-- | Infer the type of a call to a user node.
inferCall :: Name ->
             [StaticArg] ->
             [Expression] ->
             Maybe ClockExpr ->
             M (Expression, [CType])
inferCall f as es0 cl0 =
  do reqSafety   <- getUnsafeLevel
     reqTemporal <- getTemporalLevel
     cl <- case cl0 of
             Nothing -> pure Nothing
             Just c  -> case reqTemporal of
                          Node -> Just . fst <$> inferClockExpr c
                          Function ->
                            reportError $ nestedError
                               "Invalid clocked call"
                               [ "Expected to be inside a node."
                               , "We are inside a function."
                               ]

     (ni,prof) <- prepUserNodeInst f as reqSafety reqTemporal
     (es1,mp)  <- checkInputs cl [] Map.empty (nodeInputs prof) es0
     cts <- checkOuts cl mp (nodeOutputs prof)
     pure (Call ni es1 cl, cts)
  where
  renBinderClock cl mp b =
    case binderClock b of
      Nothing -> pure $ case cl of
                          Nothing -> BaseClock
                          Just c  -> KnownClock c
      Just (WhenClock r p i) ->
        -- We don't consider `cl` for binder that have an explicit clock,
        -- as it only affects the "base" clock.  Of course, the clocks will
        -- probably be inderectly affected anyway as the clock of the clock
        -- would change (etc.).
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
           (e',clk) <- checkExpr1 e (binderType b)
           sameClock c clk
           pure ( e'
                , case isClock e' of
                    Just k  -> Map.insert (binderDefines b) k mp
                    Nothing -> mp
                )
      InputConst _ t ->
        do e' <- checkConstExpr e t
           pure (e',mp)

  isClock e =
    case e of
      ERange _ e1     -> isClock e1
      Var (Unqual i)  -> Just (Right i)
      Const (Lit l) _ -> Just (Left l)
      _               -> Nothing

  checkOuts cl mp bs = mapM (checkOut cl mp) bs

  checkOut cl mp b =
    do let t = binderType b
       c <- renBinderClock cl mp b
       pure CType { cType = t, cClock = c }





-- | Infer the type of a variable.
inferVar :: Name -> M (Expression,CType)
inferVar x =
  inRange (range x) $
  case x of
    Unqual i ->
      case rnThing (nameOrigName x) of
        AVal   -> do ct <- lookupLocal i
                     pure (Var (Unqual i), ct)
        AConst -> do t1 <- lookupConst x
                     c  <- newClockVar
                     let ct = CType { cType = t1, cClock = c }
                     pure (Const (Var x) ct, ct)

        t -> panic "inferVar" [ "Identifier is not a value or a constnat:"
                              , "*** Name: " ++ showPP x
                              , "*** Thing: " ++ showPP t ]

    Qual {}  -> panic "inferVar" [ "Unexpected qualified name"
                                 , "*** Name: " ++ showPP x ]


-- | Infer the type of a literal.
inferLit :: Literal -> Type
inferLit lit =
     case lit of
       Int _   -> IntSubrange (Lit lit) (Lit lit)
       Real _  -> RealType
       Bool _  -> BoolType


-- | Validate a clock expression, and return the type of the clock.
inferClockExpr :: ClockExpr -> M (ClockExpr, CType)
inferClockExpr (WhenClock r v i) =
  inRange r $
  do ct <- lookupLocal i
     v' <- checkConstExpr v (cType ct)
     pure (WhenClock r v' i, ct)


-- | Infer the type of a branch in a @merge@.
inferMergeCase ::
  Ident                 {- ^ The clock to merge on -} ->
  Type                  {- ^ The type of the clock -} ->
  MergeCase Expression  {- ^ The branch to check -}   ->
  M (MergeCase Expression, [CType])
inferMergeCase i it (MergeCase p e) =
  do p' <- checkConstExpr p it
     let clk = KnownClock (WhenClock (range p') p' i)
     (e', cts) <- inferExpr e
     for_ cts (sameClock clk . cClock)
     pure (MergeCase p' e', cts)



-- | Infer the type of a selector.
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

           _ -> reportError $
                nestedError
               "Argument to array selector is not an array:"
                [ "Selector:" <+> pp sel
                , "Input:" <+> pp ty0
                ]

       SelectSlice _s ->
        case ty of
          ArrayType _t _sz -> notYetImplemented "array slices"
          _ -> reportError $
               nestedError
               "Arrgument to array slice is not an array:"
               [ "Selector:" <+> pp sel
               , "Input:" <+> pp ty0
               ]




