{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad(when,unless,zipWithM_,forM,forM_,replicateM)
import Text.PrettyPrint as PP
import Data.List(group,sort)

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
quickCheckDecls :: [TopDecl] -> LustreM ()
quickCheckDecls ds = runTC (go ds)
  where
  go xs = case xs of
            [] -> pure ()
            x : more -> checkTopDecl x (go more)


checkTopDecl :: TopDecl -> M a -> M a
checkTopDecl td m =
  case td of
    DeclareType tyd -> checkTypeDecl tyd m
    DeclareConst cd -> checkConstDef cd m
    DeclareNode nd -> checkNodeDecl nd m
    DeclareNodeInst _nid -> notYetImplemented "node instances"
    DeclareContract {} -> notYetImplemented "top-level contract"


checkTypeDecl :: TypeDecl -> M a -> M a
checkTypeDecl td m =
  case typeDef td of
    Nothing -> done AbstractTy
    Just dec ->
      case dec of

        IsEnum is ->
          do let ti     = typeName td
                 nty    = NamedType (Unqual ti)
                 addE i = withConst i nty
                 ty     = EnumTy (Set.fromList (map identOrigName is))
             withNamedType ti ty (foldr addE m is)

        IsStruct fs ->
          do mapM_ checkFieldType fs
             mapM_ checkDup $ group $ sort $ map fieldName fs
             done (StructTy (Map.fromList [ (fieldName f, fieldType f)
                                             | f <- fs  ]))

        IsType t ->
           do checkType t
              t1 <- tidyType t
              done (AliasTy t1)
  where
  done x = withNamedType (typeName td) x m

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


checkFieldType :: FieldType -> M ()
checkFieldType f =
  do let t = fieldType f
     checkType t
     case fieldDefault f of
       Nothing -> pure ()
       Just e  -> checkConstExpr e t

checkNodeDecl :: NodeDecl -> M a -> M a
checkNodeDecl nd k =
  do (a,b) <- check
     withNode a b k
  where
  check =
    inRange (range (nodeName nd)) $
    allowTemporal (nodeType nd == Node) $
    allowUnsafe   (nodeSafety nd == Unsafe) $
    do unless (null (nodeStaticInputs nd)) $
         notYetImplemented "static parameters"
       when (nodeExtern nd) $
         case nodeDef nd of
           Just _ -> reportError $ nestedError
                     "Extern node with a definition."
                     ["Node:" <+> pp (nodeName nd)]
           Nothing -> pure ()
       let prof = nodeProfile nd
       res <- checkInputBinders  (nodeInputs prof) $
              checkOutputBinders (nodeOutputs prof) $

         do case nodeContract nd of
              Nothing -> pure ()
              Just _  -> notYetImplemented "Node contracts"

            case nodeDef nd of
              Nothing -> unless (nodeExtern nd) $ reportError $ nestedError
                           "Missing node definition"
                           ["Node:" <+> pp (nodeName nd)]
              Just b -> checkNodeBody b
            pure (nodeName nd, (nodeSafety nd, nodeType nd, nodeProfile nd))
       solveConstraints
       pure res


checkNodeBody :: NodeBody -> M ()
checkNodeBody nb = addLocals (nodeLocals nb)
  where
  -- XXX: after checking that equations are OK individually,
  -- we should check that the LHS define proper values
  -- (e.g., no missing parts of structs/arrays etc, no repeated declarations)
  -- XXX: we also need to check that all outputs were defined.
  --      (although partial specs are also OK sometimes?)
  -- XXX: also check that that all locals have definitions
  --      (again, partial specs ok?)
  -- XXX: also, we should check that equations don't use values
  -- that are not yet defined (e.g., x = x, not OK, but x = pre x is OK)
  addLocals ls =
    case ls of
      []       -> mapM_ checkEquation (nodeEqns nb)
      l : more -> checkLocalDecl l (addLocals more)

checkLocalDecl :: LocalDecl -> M a -> M a
checkLocalDecl ld m =
  case ld of
    LocalVar b   -> checkBinder b m
    LocalConst c -> checkConstDef c m


checkConstDef :: ConstDef -> M a -> M a
checkConstDef c m =
  do t <- checkDef
     withConst (constName c) t m
  where
  checkDef =
    inRange (range (constName c)) $
    case constDef c of
      Nothing ->
        case constType c of
          Nothing -> reportError $ nestedError
                     "Constant declaration with no type or default."
                     [ "Name:" <+> pp (constName c) ]
          Just t -> do checkType t
                       pure t

      Just e ->
        do t <- case constType c of
                  Nothing -> newTVar
                  Just t  -> do checkType t
                                pure t
           checkConstExpr e t
           pure t

checkInputBinder :: InputBinder -> M a -> M a
checkInputBinder ib m =
  case ib of
    InputBinder b -> checkBinder b m
    InputConst i t ->
      do checkType t
         withConst i t m

checkBinder :: Binder -> M a -> M a
checkBinder b m =
  do c <- case binderClock b of
            Nothing -> pure BaseClock
            Just e  -> do _c <- checkClockExpr e
                          pure (KnownClock e)
     checkType (binderType b)
     let ty = CType { cType = binderType b, cClock = c }
     withLocal (binderDefines b) ty m

checkInputBinders :: [InputBinder] -> M a -> M a
checkInputBinders bs m =
  case bs of
    [] -> m
    b : more -> checkInputBinder b (checkInputBinders more m)


checkOutputBinders :: [Binder] -> M a -> M a
checkOutputBinders bs m =
  case bs of
    [] -> m
    b : more -> checkBinder b (checkOutputBinders more m)




checkType :: Type -> M ()
checkType ty =
  case ty of
    TypeRange r t -> inRange r (checkType t)
    IntType       -> pure ()
    BoolType      -> pure ()
    RealType      -> pure ()
    TVar x        -> panic "checkType" [ "Unexpected type variable:"
                                       , "*** Tvar: " ++ showPP x ]
    IntSubrange x y ->
      do checkConstExpr x IntType
         checkConstExpr y IntType
         leqConsts x y
    NamedType x ->
      do _ <- resolveNamed x
         pure ()
    ArrayType t n ->
      do checkConstExpr n IntType
         leqConsts (Lit (Int 0)) n
         checkType t


checkEquation :: Equation -> M ()
checkEquation eqn =
  enterRange $
  case eqn of
    Assert _ e ->
      onlyInputs $
        checkExpr1 e CType { cType = BoolType, cClock = BaseClock }

    Property _ e ->
      checkExpr1 e CType { cType = BoolType, cClock = BaseClock }

    IsMain _ -> pure ()

    IVC _ -> pure () -- XXX: what should we check here?

    Define ls e ->
      do lts <- mapM checkLHS ls
         checkExpr e lts

  where
  enterRange = case eqnRangeMaybe eqn of
                 Nothing -> id
                 Just r  -> inRange r


checkLHS :: LHS Expression -> M CType
checkLHS lhs =
  case lhs of
    LVar i -> lookupLocal i
    LSelect l s ->
      do t  <- checkLHS l
         t1 <- inferSelector s (cType t)
         pure t { cType = t1 }




-- | Infer the type of a constant expression.
checkConstExpr :: Expression -> Type -> M ()
checkConstExpr expr ty =
  case expr of
    ERange r e -> inRange r (checkConstExpr e ty)
    Var x      -> checkConstVar x ty
    Lit l      -> ensure (Subtype (inferLit l) ty)
    _ `When` _ -> reportError "`when` is not a constant expression."
    CondAct {} -> reportError "`condact` is not a constant expression."
    Tuple {}   -> reportError "tuples cannot be used in constant expressions."
    Array es   ->
      do elT <- newTVar
         mapM_ (`checkConstExpr` elT) es
         let n = Lit $ Int $ fromIntegral $ length es
         ensure (Subtype (ArrayType elT n) ty)

    Struct {} -> notYetImplemented "structs"
    UpdateStruct {} -> notYetImplemented "updating structs"

    Select e s ->
      do t <- newTVar
         checkConstExpr e t
         t1 <- inferSelector s t
         ensure (Subtype t1 ty)

    WithThenElse e1 e2 e3 ->
      do checkConstExpr e1 BoolType
         checkConstExpr e2 ty
         checkConstExpr e3 ty

    Merge {}   -> reportError "`merge` is not a constant expression."
    Call {}   -> reportError "constant expressions do not support calls."

-- | Check that the expression has the given type.
checkExpr1 :: Expression -> CType -> M ()
checkExpr1 e t = checkExpr e [t]




{- | Check if an expression has the given type.
Tuples and function calls may return multiple results,
which is why we provide multiple clocked types. -}
checkExpr :: Expression -> [CType] -> M ()
checkExpr expr tys =
  case expr of
    ERange r e -> inRange r (checkExpr e tys)

    Var x      -> inRange (range x) $
                  do ty <- one tys
                     checkVar x ty

    Lit l      -> do ty <- one tys
                     let lt = inferLit l
                     ensure (Subtype lt (cType ty))

    e `When` c ->
      do checkTemporalOk "when"
         c1 <- checkClockExpr c -- `c1` is the clock of c

         tys1 <- forM tys $ \ty ->
                   do sameClock (cClock ty) (KnownClock c)
                      pure ty { cClock = c1 }

         checkExpr e tys1

    CondAct c e mb ->
      do checkTemporalOk "when"
         c1 <- checkClockExpr c -- `c1` is the clock of c
         forM_ mb $ \d -> checkExpr d tys

         tys1 <- forM tys $ \ty ->
                   do sameClock (cClock ty) c1
                      pure ty { cClock = c1 }

         checkExpr e tys1

    Tuple es
      | have == need -> zipWithM_ checkExpr1 es tys
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
         mapM_ (`checkExpr1` elCT) es


    Select e s ->
      do ty <- one tys
         recT <- newTVar
         checkExpr1 e ty { cType = recT }
         t1 <- inferSelector s recT
         ensure (Subtype t1 (cType ty))

    Struct {} -> notYetImplemented "struct"
    UpdateStruct {} -> notYetImplemented "update struct"

    WithThenElse e1 e2 e3 ->
      do checkConstExpr e1 BoolType
         checkExpr e2 tys
         checkExpr e3 tys

    Merge i as ->
      do t <- lookupLocal i
         mapM_ (sameClock (cClock t) . cClock) tys
         let it      = cType t
             ts      = map cType tys
             check c = checkMergeCase i c it ts
         mapM_ check as

    Call (NodeInst call as) es
      | not (null as) -> notYetImplemented "Call with static arguments."

      -- Special case for @^@ because its second argument is a constant
      -- expression, not an ordinary one.
      | CallPrim r (Op2 Replicate) <- call ->
        inRange r $
        case es of
          [e1,e2] ->
            do ty <- one tys
               checkConstExpr e2 IntType
               elT <- newTVar
               checkExpr e1 [ty { cType = elT }]
               ensure (Subtype (ArrayType elT e2) (cType ty))
          _ -> reportError $ text (showPP call ++ " expexts 2 arguments.")

      | otherwise ->
        case call of
          CallUser f      -> checkCall f es tys
          CallPrim _ prim -> checkPrim prim es tys

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



-- | Infer the type of a call to a user-defined node.
checkCall :: Name -> [Expression] -> [CType] -> M ()
checkCall f es0 tys =
  do (safe,ty,prof) <- lookupNodeProfile f
     case safe of
       Safe   -> pure ()
       Unsafe -> checkUnsafeOk (pp f)
     case ty of
       Node     -> checkTemporalOk ("node" <+> pp f)
       Function -> pure ()
     mp   <- checkInputs Map.empty (nodeInputs prof) es0
     checkOuts mp (nodeOutputs prof)
  where
  renBinderClock mp b =
    case binderClock b of
      Nothing -> pure BaseClock
      Just (WhenClock r p i) ->
        case Map.lookup i mp of
          Just j  -> pure (KnownClock (WhenClock r p j))
          Nothing -> reportError $ text ("Parameter for clock " ++ showPP i ++
                                                      "is not an identifier.")

  checkInputs mp is es =
    case (is,es) of
      ([],[]) -> pure mp
      (b:bs,a:as) -> do mp1 <- checkIn mp b a
                        checkInputs mp1 bs as
      _ -> reportError $ text ("Bad arity in call to " ++ showPP f)

  checkIn mp ib e =
    case ib of
      InputBinder b ->
        do c <- renBinderClock mp b
           checkExpr1 e CType { cClock = c, cType = binderType b }
           pure $ case isIdent e of
                    Just k  -> Map.insert (binderDefines b) k mp
                    Nothing -> mp
      InputConst _ t ->
        do checkConstExpr e t
           pure mp

  isIdent e =
    case e of
      ERange _ e1    -> isIdent e1
      Var (Unqual i) -> Just i
      _              -> Nothing

  checkOuts mp bs
    | have == need = zipWithM_ (checkOut mp) bs tys
    | otherwise = reportError $ nestedError
                  "Arity mistmatch in function call."
                  [ "Function:" <+> pp f
                  , "Returns:" <+> text (show have) <+> "restuls"
                  , "Expected:" <+> text (show need) <+> "restuls" ]
      where have = length bs
            need = length tys


  checkOut mp b ty =
    do let t = binderType b
       c <- renBinderClock mp b
       subCType CType { cClock = c, cType = t } ty


-- | Infer the type of a call to a primitive node.
checkPrim :: PrimNode -> [Expression] -> [CType] -> M ()
checkPrim prim es tys =
  case prim of

    Iter {} -> notYetImplemented "iterators."

    Op1 op1 ->
      case es of
        [e] -> checkOp1 op1 e tys
        _   -> reportError $ text (showPP op1 ++ " expects 1 argument.")

    Op2 op2 ->
      case es of
        [e1,e2] -> checkOp2 op2 e1 e2 tys
        _ -> reportError $ text (showPP op2 ++ " expects 2 arguments.")

    ITE ->
      case es of
        [e1,e2,e3] ->
          do c <- case tys of
                    []     -> newClockVar -- XXX: or report error?
                    t : ts -> do let c = cClock t
                                 mapM_ (sameClock c . cClock) ts
                                 pure c
             checkExpr1 e1 CType { cClock = c, cType = BoolType }
             checkExpr e2 tys
             checkExpr e3 tys

        _ -> reportError "`if-then-else` expects 3 arguments."


    -- IMPORTANT: For the moment these all work with bools, so we
    -- just do them in one go.  THIS MAY CHANGE if we add
    -- other operators!
    OpN _ ->
      do ty <- one tys
         let bool = ty { cType = BoolType }
         mapM_ (`checkExpr1` bool) es
         ensure (Subtype BoolType (cType ty))



-- | Infer the type for a branch of a merge.
checkMergeCase :: Ident -> MergeCase Expression -> Type -> [Type] -> M ()
checkMergeCase i (MergeCase p e) it ts =
  do checkConstExpr p it
     checkExpr e (map toCType ts)
  where
  clk       = KnownClock (WhenClock (range p) p i)
  toCType t = CType { cClock = clk, cType = t }

-- | Types of unary opertaors.
checkOp1 :: Op1 -> Expression -> [CType] -> M ()
checkOp1 op e tys =
  case op of
    Pre -> do checkTemporalOk "pre"
              checkExpr e tys

    Current ->
      do checkTemporalOk "current"
         tys1 <- forM tys $ \ty ->
                    do c <- newClockVar
                       pure ty { cClock = c }
         checkExpr e tys1

         -- By now we should have figured out the missing clock,
         -- so check straight away
         let checkClock ty newTy =
                sameClock (cClock ty) =<< clockParent (cClock newTy)
         zipWithM_ checkClock tys tys1

    Not ->
      do ty <- one tys
         checkExpr1 e ty { cType = BoolType }
         ensure (Subtype BoolType (cType ty))

    Neg ->
      do ty <- one tys
         t <- newTVar
         checkExpr1 e ty { cType = t }
         ensure (Arith1 "-" t (cType ty))

    IntCast ->
      do ty <- one tys
         checkExpr1 e ty { cType = RealType }
         ensure (Subtype IntType (cType ty))

    FloorCast ->
      do ty <- one tys
         checkExpr1 e ty { cType = RealType }
         ensure (Subtype IntType (cType ty))

    RealCast ->
      do ty <- one tys
         checkExpr1 e ty { cType = IntType }
         ensure (Subtype RealType (cType ty))


-- | Types of binary operators.
checkOp2 :: Op2 -> Expression -> Expression -> [CType] -> M ()
checkOp2 op2 e1 e2 tys =
  case op2 of
    FbyArr   -> do checkTemporalOk "->"
                   checkExpr e1 tys
                   checkExpr e2 tys

    Fby      -> do checkTemporalOk "fby"
                   checkExpr e1 tys
                   checkExpr e2 tys

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

    Concat ->
      do ty <- one tys
         a0 <- newTVar
         checkExpr1 e1 ty { cType = a0 }
         b0 <- newTVar
         checkExpr1 e2 ty { cType = b0 }
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


  where
  bool2     = do ty <- one tys
                 checkExpr1 e1 ty { cType = BoolType }
                 checkExpr1 e2 ty { cType = BoolType }
                 ensure (Subtype BoolType (cType ty))

  infer2    = do ty <- one tys
                 t1 <- newTVar
                 checkExpr1 e1 ty { cType = t1 }
                 t2 <- newTVar
                 checkExpr1 e2 ty { cType = t2 }
                 pure (t1,t2,ty)

  ordRel op = do (t1,t2,ty) <- infer2
                 ensure (CmpOrd op t1 t2)
                 ensure (Subtype BoolType (cType ty))

  arith x   = do (t1,t2,ty) <- infer2
                 ensure (Arith2 x t1 t2 (cType ty))

  eqRel op  = do ty  <- one tys
                 n   <- exprArity e1
                 tv1s <- replicateM n newTVar
                 tv2s <- replicateM n newTVar
                 let toTy t = ty { cType = t }
                 checkExpr e1 (map toTy tv1s)
                 checkExpr e2 (map toTy tv2s)
                 zipWithM_ (\t1 t2 -> ensure (CmpEq op t1 t2)) tv1s tv2s
                 ensure (Subtype BoolType (cType ty))



-- | Check the type of a variable.
checkVar :: Name -> CType -> M ()
checkVar x ty =
  case x of
    Unqual i ->
      case rnThing (nameOrigName x) of
        AVal   -> do c <- lookupLocal i
                     subCType c ty
        AConst -> checkConstVar x (cType ty)
        t -> panic "checkVar" [ "Identifier is not a value or a constnat:"
                              , "*** Name: " ++ showPP x
                              , "*** Thing: " ++ showPP t ]

    Qual {}  -> panic "checkVar" [ "Unexpected qualified name"
                                 , "*** Name: " ++ showPP x ]



-- | Check the type of a named constnat.
checkConstVar :: Name -> Type -> M ()
checkConstVar x ty = inRange (range x) $
                     do t1 <- lookupConst x
                        ensure (Subtype t1 ty)

-- | Infer the type of a literal.
inferLit :: Literal -> Type
inferLit lit =
     case lit of
       Int _   -> IntSubrange (Lit lit) (Lit lit)
       Real _  -> RealType
       Bool _  -> BoolType

-- | Check a clock expression, and return its clock.
checkClockExpr :: ClockExpr -> M IClock
checkClockExpr (WhenClock r v i) =
  inRange r $
    do ct <- lookupLocal i
       checkConstExpr v (cType ct)
       pure (cClock ct)

--------------------------------------------------------------------------------

inferSelector :: Selector Expression -> Type -> M Type
inferSelector sel ty0 =
  do ty <- tidyType ty0
     case sel of
       SelectField f ->
         case ty of
           NamedType a ->
             do fs <- lookupStruct a
                case Map.lookup f fs of
                  Just t  -> pure t
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
             do checkConstExpr n IntType
                -- XXX: check that 0 <= && n < sz ?
                pure t

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








