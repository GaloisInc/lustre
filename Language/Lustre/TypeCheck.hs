{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad(when,unless,zipWithM_,zipWithM)
import Text.PrettyPrint as PP
import Data.List(group,sort)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic
import Language.Lustre.TypeCheck.Monad



quickCheckDecls :: [TopDecl] -> Either Doc ()
quickCheckDecls = runTC . go
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


checkTypeDecl :: TypeDecl -> M a -> M a
checkTypeDecl td m =
  case typeDef td of
    Nothing -> done AbstractTy
    Just dec ->
      case dec of

        IsEnum is ->
          do mapM_ uniqueConst is
             let n      = typeName td
                 addE i = withConst i (NamedType (Unqual n))
             withNamedType n (EnumTy (Set.fromList is)) (foldr addE m is)

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
       Just e  -> do t1 <- inferConstExpr e
                     subType t1 t

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
       checkBinders (nodeInputs prof ++ nodeOutputs prof) $
         do case nodeDef nd of
              Nothing -> unless (nodeExtern nd) $ reportError $ nestedError
                           "Missing node definition"
                           ["Node:" <+> pp (nodeName nd)]
              Just b -> checkNodeBody b
            pure (nodeName nd, (nodeSafety nd, nodeType nd, nodeProfile nd))



checkNodeBody :: NodeBody -> M ()
checkNodeBody nb = addLocals (nodeLocals nb)
  where
  -- XXX: check for duplicate constant declarations.
  -- XXX: after checking that equations are OK individually,
  -- we should check that the LHS define proper values
  -- (e.g., no missing parts of structs/arrays etc)
  -- XXX: we also need to check that all outputs were defined.
  -- XXX: also check that that all locals have definitions
  -- XXX: also check that there aren't any extra equations.
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
  inRange (range (constName c)) $
  case constDef c of
    Nothing ->
      case constType c of
        Nothing -> reportError $ nestedError
                   "Constant declaration with no type or default."
                   [ "Name:" <+> pp (constName c) ]
        Just t -> do checkType t
                     done t

    Just e ->
      do t1 <- inferConstExpr e
         case constType c of
           Nothing -> done t1
           Just t -> do checkType t
                        subType t1 t
                        done t
  where
  done t = withConst (constName c) t m

checkBinder :: Binder -> M a -> M a
checkBinder b m =
  do c <- case binderClock b of
            Nothing -> pure BaseClock
            Just e  -> do _c <- checkClockExpr e
                          pure (KnownClock e)
     checkType (binderType b)
     let ty = CType { cType = binderType b, cClock = c }
     withLocal (binderDefines b) ty m

checkBinders :: [Binder] -> M a -> M a
checkBinders bs m =
  case bs of
    [] -> m
    b : more -> checkBinder b (checkBinders more m)


checkType :: Type -> M ()
checkType ty =
  case ty of
    TypeRange r t -> inRange r (checkType t)
    IntType       -> pure ()
    BoolType      -> pure ()
    RealType      -> pure ()
    IntSubrange x y ->
      do lt <- inferConstExpr x
         subType lt IntType
         ut <- inferConstExpr y
         subType ut IntType
         leqConsts x y
    NamedType x ->
      do _ <- resolveNamed x
         pure ()
    ArrayType t n ->
      do nt <- inferConstExpr n
         subType nt IntType
         leqConsts (Lit (Int 0)) n
         checkType t


checkEquation :: Equation -> M ()
checkEquation eqn =
  enterRange $
  case eqn of
    Assert _ e ->
      do t <- inferExpr1 BaseClock e
         t `subType` BoolType
         -- XXX: maybe make sure that this only uses inputs
         -- as nothing else is under the caller's control.

    Property _ e ->
      do t <- inferExpr1 BaseClock e
         t `subType` BoolType

    IsMain _ -> pure ()

    IVC _ -> pure () -- XXX: what should we check here?

    Define ls e ->
      do lts <- mapM checkLHS ls
         rts <- inferExpr (map cClock lts) e
         zipWithM_ subType   (map cType lts)  rts

  where
  enterRange = case eqnRangeMaybe eqn of
                 Nothing -> id
                 Just r  -> inRange r


checkLHS :: LHS Expression -> M CType
checkLHS lhs =
  case lhs of
    LVar i -> lookupIdent i
    LSelect l s ->
      do t  <- checkLHS l
         t1 <- checkSelector (cType t) s
         pure t { cType = t1 }




-- | Infer the type of a constant expression.
inferConstExpr :: Expression -> M Type
inferConstExpr expr =
  case expr of
    ERange r e -> inRange r (inferConstExpr e)
    Var x      -> lookupConst x
    Lit l      -> pure (inferLit l)
    _ `When` _ -> reportError "`when` is not a constant expression."
    Tuple {}   -> reportError "tuples cannot be used in constant expressions."
    Array es   ->
      do ts <- mapM inferConstExpr es
         t  <- case ts of
                 []     -> notYetImplemented "empty arrays"
                 a : bs -> typeLUBs a bs
         let n = Lit $ Int $ fromIntegral $ length es
         pure (ArrayType t n)

    Struct {} -> undefined

    Select e s ->
      do t <- inferConstExpr e
         checkSelector t s

    WithThenElse e1 e2 e3 ->
      do t <- inferConstExpr e1
         subType t BoolType
         x <- inferConstExpr e2
         y <- inferConstExpr e3
         typeLUB x y

    Merge {}   -> reportError "`merge` is not a constant expression."
    CallPos {} -> reportError "constant expressions do not support calls."


-- | Infer the type of an expression that does not return a tuple.
inferExpr1 :: IClock -> Expression -> M Type
inferExpr1 c e =
  do ~[t] <- inferExpr [c] e
     pure t


-- | Infer the type of an expression.  Tuples and function calls may return
-- multiple results, which is why we return a list of types.
inferExpr :: [IClock] -> Expression -> M [Type]
inferExpr clks expr =
  case expr of
    ERange r e -> inRange r (inferExpr clks e)

    Var x      -> inRange (range x) $
                  do clk <- one clks
                     t   <- inferVar clk x
                     pure [t]

    Lit l      -> pure [ inferLit l ]

    e `When` c ->
      do checkTemporalOk "when"
         c1  <- checkClockExpr c -- `c1` is the clock of c
         t   <- inferExpr1 c1 e
         clk <- one clks
         sameClock clk (KnownClock c)
         pure [t]

    Tuple es
      | have == need -> zipWithM inferExpr1 clks es
      | otherwise    -> reportError $ nestedError "Arity mismatch"
                          [ "Expected arity:" <+> text (show need)
                          , "Actual arity:" <+> text (show have) ]
      where have = length es
            need = length clks

    Array es ->
      do clk <- one clks
         ts <- mapM (inferExpr1 clk) es
         t  <- case ts of
                 t : more -> typeLUBs t more
                 []       -> reportError "Cannot infer type of an empty array"
         let n = Lit $ Int $ fromIntegral $ length es
         pure [ ArrayType t n ]

    Select e s ->
      do clk <- one clks
         t   <- inferExpr1 clk e
         res <- checkSelector t s
         pure [res]

    Struct {} -> undefined

    WithThenElse e1 e2 e3 ->
      do t1 <- inferConstExpr e1
         subType t1 BoolType
         a  <- inferExpr clks e2
         b  <- inferExpr clks e3
         zipWithM typeLUB a b

    Merge i as ->
      do t   <- lookupIdent i
         mapM_ (sameClock (cClock t)) clks
         let ar = length clks

         ats <- mapM (inferMergeCase ar i (cType t)) as
         case ats of
           [] -> reportError "Empty `merge`"
           r : more -> typeLUBss r more

    CallPos (NodeInst call as) es
      | not (null as) -> notYetImplemented "Call with static arguments."

      -- Special case for @^@ because its second argument is a constant
      -- expression, not an ordinary one.
      | CallPrim r (Op2 Replicate) <- call ->
        inRange r $
        case es of
          [e1,e2] ->
            do clk <- one clks
               t1  <- inferExpr1 clk e1
               t2  <- inferConstExpr e2
               t2 `subType` IntType
               pure [ ArrayType t1 e2 ]
          _ -> reportError $ text (showPP call ++ " expexts 2 arguments.")

      | otherwise ->
        case call of
          CallUser f      -> inferCall clks f es
          CallPrim _ prim -> inferPrim clks prim es

-- | Assert that a given expression has only one type (i.e., is not a tuple)
one :: [a] -> M a
one xs =
  case xs of
    [x] -> pure x
    _   -> reportError $
           nestedError "Arity mismatch."
            [ "Arity 1:" <+> "1"
            , "Arity 2:" <+> text (show (length xs)) ]



-- | Infer the type of a call to a user-defined node.
inferCall :: [IClock] -> Name -> [Expression] -> M [Type]
inferCall clks f es0 =
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

  checkIn mp b e =
    do c <- renBinderClock mp b
       t <- inferExpr1 c e
       subType t (binderType b)
       pure $ case isIdent e of
                Just k  -> Map.insert (binderDefines b) k mp
                Nothing -> mp

  isIdent e =
    case e of
      ERange _ e1    -> isIdent e1
      Var (Unqual i) -> Just i
      _              -> Nothing

  checkOuts mp bs
    | have == need = zipWithM (checkOut mp) clks bs
    | otherwise = reportError $ nestedError
                  "Arity mistmatch in function call."
                  [ "Function:" <+> pp f
                  , "Returns:" <+> text (show have) <+> "restuls"
                  , "Expected:" <+> text (show need) <+> "restuls" ]
      where have = length bs
            need = length clks


  checkOut mp clk b =
    do let t = binderType b
       c <- renBinderClock mp b
       sameClock clk c
       pure t


-- | Infer the type of a call to a primitive node.
inferPrim :: [IClock] -> PrimNode -> [Expression] -> M [Type]
inferPrim clks prim es =
  case prim of

    Iter {} -> notYetImplemented "iterators."

    Op1 op1 ->
      case es of
        [e] -> do clk <- one clks
                  oneRes =<< checkOp1 clk op1 e
        _   -> reportError $ text (showPP op1 ++ " expects 1 argument.")

    -- IMPORTANT: all binary operators work with the same clocks,
    -- so we do the clock checking here.  THIS MAY CHANGE if we add more ops!
    Op2 op2 ->
      do ts <- withSameClock
         case ts of
           [t1,t2] -> oneRes =<< checkOp2 op2 t1 t2
           _ -> reportError $ text (showPP op2 ++ " expects 2 arguments.")

    ITE ->
      do ts <- withSameClock
         case ts of
           [t1,t2,t3] ->
              do subType t1 BoolType
                 oneRes =<< typeLUB t2 t3
           _ -> reportError "`if-then-else` expects 3 arguments."

    -- IMPORTANT: For the moment these all work with bools, so we
    -- just do them in one go.  THIS MAY CHANGE if we add
    -- other operators!
    OpN _ ->
      do ts <- withSameClock
         mapM_ (`subType` BoolType) ts
         oneRes BoolType

  where
  withSameClock = do clk <- one clks
                     mapM (inferExpr1 clk) es

  oneRes t = pure [t]


-- | Infer the type for a branch of a merge.
inferMergeCase :: Int -> Ident -> Type -> MergeCase -> M [Type]
inferMergeCase ar i it (MergeCase p e) =
  do t <- inferConstExpr p
     subType t it
     let clk = KnownClock (WhenClock (range p) p i)
     inferExpr (replicate ar clk) e


-- | Types of unary opertaors.
checkOp1 :: IClock -> Op1 -> Expression -> M Type
checkOp1 clk op e =
  case op of
    Pre -> do checkTemporalOk "pre"
              inferExpr1 clk e

    Current ->
      do checkTemporalOk "current"
         c <- newClockVar
         t <- inferExpr1 c e
         -- By now we should have figured out the missing clock,
         -- so check straight away
         sameClock clk =<< clockParent c
         pure t

    Not ->
      do t <- inferExpr1 clk e
         subType t BoolType
         pure BoolType

    Neg -> do t <- inferExpr1 clk e
              classArith1 "-" t

    IntCast ->
      do t <- inferExpr1 clk e
         subType t RealType
         pure IntType

    RealCast ->
      do t <- inferExpr1 clk e
         subType t IntType
         pure RealType


-- | Types of binary operators.
checkOp2 :: Op2 -> Type -> Type -> M Type
checkOp2 op2 tx ty =
  case op2 of
    FbyArr   -> checkTemporalOk "->"  >> typeLUB tx ty
    Fby      -> checkTemporalOk "fby" >> typeLUB tx ty

    And      -> bool2
    Or       -> bool2
    Xor      -> bool2
    Implies  -> bool2

    Eq       -> classEq tx ty >> pure BoolType
    Neq      -> classEq tx ty >> pure BoolType

    Lt       -> classOrd "<"  tx ty >> pure BoolType
    Leq      -> classOrd "<=" tx ty >> pure BoolType
    Gt       -> classOrd ">"  tx ty >> pure BoolType
    Geq      -> classOrd ">=" tx ty >> pure BoolType

    Add      -> classArith2 "+"   tx ty
    Sub      -> classArith2 "-"   tx ty
    Mul      -> classArith2 "*"   tx ty
    Div      -> classArith2 "/"   tx ty
    Mod      -> classArith2 "mod" tx ty

    Power    -> notYetImplemented "Exponentiation"

    Replicate -> panic "checkOp2" [ "`replicate` should have been checked."]

    Concat ->
      do t1 <- tidyType tx
         t2 <- tidyType ty
         case (t1,t2) of
           (ArrayType elT1 n, ArrayType elT2 m) ->
             do elT <- typeLUB elT1 elT2
                l   <- addConsts n m
                pure (ArrayType elT l)
           _ -> reportError "`|` expects two arrays."

  where
  bool2 = do subType tx BoolType
             subType ty BoolType
             pure BoolType



-- | Infer the type of a variable.
inferVar :: IClock -> Name -> M Type
inferVar clk x =
  case x of
    Unqual i -> do mb <- lookupIdentMaybe i
                   case mb of
                     Just c  -> do sameClock clk (cClock c)
                                   pure (cType c)
                     Nothing -> inferConstVar x
    Qual {}  -> inferConstVar x

-- | Infer the type for a named constant.
inferConstVar :: Name -> M Type
inferConstVar x = inRange (range x) (lookupConst x)

-- | Infer the type of a literal.
inferLit :: Literal -> Type
inferLit lit =
     case lit of
       Int _   -> IntType
       Real _  -> RealType
       Bool _  -> BoolType

-- | Check a clock expression, and return its clock.
checkClockExpr :: ClockExpr -> M IClock
checkClockExpr (WhenClock r v i) =
  inRange r $
  do t  <- inferConstExpr v
     ct <- lookupIdent i
     subType t (cType ct)
     pure (cClock ct)

--------------------------------------------------------------------------------

checkSelector :: Type -> Selector Expression -> M Type
checkSelector ty0 sel =
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

           _ -> reportError $
                nestedError
                  "Argument to struct selector is not a struct:"
                  [ "Selector:" <+> pp sel
                  , "Input:" <+> pp ty0
                  ]

       SelectElement n ->
         case ty of
           ArrayType t _sz ->
             do i <- inferConstExpr n
                subType i IntType
                -- XXX: check that 0 <= && n < sz ?
                pure t
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





--------------------------------------------------------------------------------
-- Comparsions of types

sameType :: Type -> Type -> M ()
sameType x y =
  do s <- tidyType x
     t <- tidyType y
     case (s,t) of
      (NamedType a,   NamedType b)   | a == b -> pure ()
      (ArrayType a m, ArrayType b n) -> sameConsts m n >> sameType a b

      (IntType,IntType)   -> pure ()
      (RealType,RealType) -> pure ()
      (BoolType,BoolType) -> pure ()
      (IntSubrange a b, IntSubrange c d) ->
        sameConsts a c >> sameConsts b d
      _ -> reportError $ text ("Type mismatch: " ++ showPP x ++ " and " ++ showPP y)


sameTypes :: [Type] -> [Type] -> M ()
sameTypes xs ys =
  case (xs,ys) of
    ([],[]) -> pure ()
    (a:as,b:bs) -> sameType a b >> sameTypes as bs
    _ -> reportError "Arity mismatch."


-- Subtype is like "subset"
subType :: Type -> Type -> M ()
subType x y =
  do s <- tidyType x
     t <- tidyType y
     case (s,t) of
       (IntSubrange {}, IntType) -> pure ()
       (IntSubrange a b, IntSubrange c d) -> leqConsts c a >> leqConsts b d
       (ArrayType a m, ArrayType b n) ->
          do sameConsts m n
             subType a b
       _ -> sameType s t


typeLUB :: Type -> Type -> M Type
typeLUB x y =
  do s <- tidyType x
     t <- tidyType y
     case (s,t) of
       (IntSubrange {}, IntType) -> pure IntType
       (IntType, IntSubrange {}) -> pure IntType
       (IntSubrange a b, IntSubrange c d) ->
          do l <- minConsts a c
             u <- maxConsts b d
             pure (IntSubrange l u)

       (IntType,IntType)   -> pure x
       (BoolType,BoolType) -> pure x
       (RealType,RealType) -> pure x
       (NamedType a, NamedType b) | a == b -> pure x
       (ArrayType a b, ArrayType c d) ->
          do sameConsts b d
             elT <- typeLUB a c
             pure (ArrayType elT b)
       _ -> reportError $ nestedError
            "Incompatable types:"
            [ "Type 1:" <+> pp x
            , "Type 2:" <+> pp y
            ]


typeLUBs :: Type -> [Type] -> M Type
typeLUBs t more =
  case more of
    [] -> pure t
    x : xs -> do y <- typeLUB t x
                 typeLUBs y xs

typeLUBss :: [Type] -> [[Type]] -> M [Type]
typeLUBss xs yss =
  case (xs,yss) of
    (a : as, bs : bss) -> do r <- typeLUBs a bs
                             rs <- typeLUBss as bss
                             pure (r : rs)
    ([],[]) -> pure []
    _ -> reportError "Arity error"




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
       KnownClock (WhenClock _ _ i) -> cClock <$> lookupIdent i
       ClockVar _ -> reportError "Failed to infer the expressions's clock"



--------------------------------------------------------------------------------
-- Expressions

intConst :: Expression -> M Integer
intConst x =
  case x of
    ERange _ y  -> intConst y
    Lit (Int a) -> pure a
    _ -> reportError $ nestedError
           "Constant expression is not a concrete integer."
           [ "Expression:" <+> pp x ]

binConst :: (Integer -> Integer -> Integer) ->
            Expression -> Expression -> M Expression
binConst f e1 e2 =
  do x <- intConst e1
     y <- intConst e2
     pure $ Lit $ Int $ f x y

cmpConsts :: Doc ->
             (Integer -> Integer -> Bool) ->
             Expression -> Expression -> M ()
cmpConsts op p e1 e2 =
  do x <- intConst e1
     y <- intConst e2
     unless (p x y) $ reportError $ pp x <+> "is not" <+> op <+> pp y

addConsts :: Expression -> Expression -> M Expression
addConsts = binConst (+)

minConsts :: Expression -> Expression -> M Expression
minConsts = binConst min

maxConsts :: Expression -> Expression -> M Expression
maxConsts = binConst max

sameConsts :: Expression -> Expression -> M ()
sameConsts e1 e2 =
  case (e1,e2) of
    (ERange _ x,_)  -> sameConsts x e2
    (_, ERange _ x) -> sameConsts e1 x
    (Var x, Var y) | x == y -> pure ()
    (Lit x, Lit y) | x == y -> pure ()
    _ -> reportError $ nestedError
           "Constants do not match"
           [ "Constant 1:" <+> pp e1
           , "Constant 2:" <+> pp e2
           ]

leqConsts :: Expression -> Expression -> M ()
leqConsts = cmpConsts "less-than, or equal to" (<=)



--------------------------------------------------------------------------------

-- | Are these types comparable of equality
classEq :: Type -> Type -> M ()
classEq s t =
  do _ <- typeLUB s t
     pure ()

-- | Are these types comparable for ordering
classOrd :: Doc -> Type -> Type -> M ()
classOrd op s' t' =
  do s <- tidyType s'
     t <- tidyType t'
     case (s,t) of
       (RealType,RealType) -> pure ()
       _ | isIntegral s && isIntegral t -> pure ()
         | otherwise ->
          reportError $ nestedError
            "Invalid use of comparison operator:"
            [ "Operator:" <+> op
            , "Input 1:" <+> pp s'
            , "Input 2:" <+> pp t'
            ]

-- | Can we do unary arithemtic on this type, and if so what's the
-- type of the answer.
classArith1 :: Doc -> Type -> M Type
classArith1 op t0 =
  do ty <- tidyType t0
     case ty of
       IntType        -> pure IntType
       RealType       -> pure RealType
       IntSubrange {} -> pure IntType
       _ -> reportError $ nestedError
          "Invalid use of unary arithemtic operator:"
          [ "Operaotr:" <+> op
          , "Input:"    <+> pp t0
          ]


-- | Can we do binary arithemtic on this type, and if so what's the
-- type of the answer.
classArith2 :: Doc -> Type -> Type -> M Type
classArith2 op s t =
  do s1 <- tidyType s
     t1 <- tidyType t
     case (s1,t1) of
       (RealType,RealType) -> pure RealType
       _ | isIntegral s1 && isIntegral t1 -> pure IntType
         | otherwise ->
          reportError $ nestedError
            "Invalid use of binary arithmetic operator:"
            [ "Operator:" <+> op
            , "Input 1:"  <+> pp s
            , "Input 2:"  <+> pp t
            ]

-- | Is this an integer-like type.
isIntegral :: Type -> Bool
isIntegral ty =
  case ty of
    IntType -> True
    IntSubrange {} -> True
    _ -> False





