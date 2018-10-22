{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck where

import qualified Data.Map as Map
import Control.Monad((<=<),unless,zipWithM_)
import Text.PrettyPrint

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic
import Language.Lustre.TypeCheck.Monad



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
                 []     -> reportError "XXX: Empty arrays"
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

-- | Infer the type of an expression.  Tuples and function calls may return
-- multiple results, which is why we return a list of types.
inferExpr :: Expression -> M [CType]
inferExpr expr =
  case expr of
    ERange r e -> inRange r (inferExpr e)

    Var x      -> do t <- inferVar x
                     pure [t]

    Lit l      -> pure [CType { cType = inferLit l, cClock = ConstExpr }]

    e `When` c ->
      do t  <- oneType =<< inferExpr e
         c1 <- checkClockExpr c -- `c1` is the clock of c
         _  <- sameClock (cClock t) c1
         pure [ CType { cType  = cType t
                      , cClock = KnownClock c } ]

    Tuple es -> mapM (oneType <=< inferExpr) es

    Array es ->
      do ts <- mapM (oneType <=< inferExpr) es
         t  <- case ts of
                 t : more -> ctypeLUBs t more
                 []       -> reportError "Cannot infer type of an empty array"
         let n = Lit $ Int $ fromIntegral $ length es
         pure [ t { cType = ArrayType (cType t) n } ]

    Select e s ->
      do t  <- oneType =<< inferExpr e
         t1 <- checkSelector (cType t) s
         pure [ t { cType = t1 } ]


    Struct {} -> undefined

    WithThenElse e1 e2 e3 ->
      do t1 <- inferConstExpr e1
         subType t1 BoolType
         a  <- inferExpr e2
         b  <- inferExpr e3
         sameCTypes a b

    Merge i as ->
      do t   <- lookupIdent i
         ats <- mapM (inferMergeCase i t) as
         rs  <- case ats of
                  [] -> reportError "Empty `merge`"
                  r : more -> typeLUBss r more

         pure [ CType { cType = r, cClock = cClock t } | r <- rs ]


    CallPos (NodeInst call as) es
      | not (null as) -> reportError "Unexpected static arguments."

      -- Special case for @^@ because its second argument is a constant
      -- expression, not an ordinary one.
      | CallPrim r (Op2 Replicate) <- call ->
        inRange r $
        case es of
          [e1,e2] ->
            do t1 <- oneType =<< inferExpr e1
               t2 <- tidyType =<< inferConstExpr e2
               unless (isIntegral t2) $
                  reportError "The 2nd argument of replicate must be integral."
               pure [ t1 { cType = ArrayType (cType t1) e2 } ]
          _ -> reportError $ text (showPP call ++ " expexts 2 arguments.")

      | otherwise ->
        do ts <- mapM (oneType <=< inferExpr) es
           case call of
             CallUser f -> checkCall f (zip es ts)
             CallPrim r prim ->
                do t <- inRange r (checkPrim prim ts)
                   pure [t]

-- | Assert that a given expression has only one type (i.e., is not a tuple)
oneType :: [CType] -> M CType
oneType xs =
  case xs of
    [x] -> pure x
    _   -> reportError "Arity mismatch."

-- | Infer the type of a call to a user-defined node.
checkCall :: Name -> [(Expression,CType)] -> M [CType]
checkCall f ts =
  do prof <- lookupNodeProfile f
     mp   <- checkInputs Map.empty (nodeInputs prof) ts
     mapM (checkOut mp) (nodeOutputs prof)
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

  checkIn mp b (e,et) =
    do let t = binderType b
       subType (cType et) t
       _ <- sameClock (cClock et) =<< renBinderClock mp b
       pure $ case isIdent e of
                Just k  -> Map.insert (binderDefines b) k mp
                Nothing -> mp

  isIdent e =
    case e of
      ERange _ e1    -> isIdent e1
      Var (Unqual i) -> Just i
      _              -> Nothing

  checkOut mp b =
    do let t = binderType b
       c <- renBinderClock mp b
       pure CType { cType = t, cClock = c }


-- | Infer the type of a call to a primitive node.
checkPrim :: PrimNode -> [CType] -> M CType
checkPrim prim ts =
  case prim of

    Iter {} -> reportError "XXX: Iter"

    Op1 op1 ->
      case ts of
        [t] -> checkOp1 op1 t
        _   -> reportError $ text (showPP op1 ++ " expects 1 argument.")

    Op2 op2 ->
       case ts of
         [t1,t2] -> checkOp2 op2 t1 t2
         _ -> reportError $ text (showPP op2 ++ " expects 2 arguments.")

    ITE ->
      case ts of
        [t1,t2,t3] ->
           do subType (cType t1) BoolType
              c <- sameClock (cClock t1) (cClock t2)
              t <- sameCType t2 t3
              pure $ if isConstExpr c then t else t { cClock = c }
        _ -> reportError "`if-then-else` expects 3 arguments."

    -- IMPORTANT: For the moment these all work with bools, so we
    -- just do them in one go.  This may change if we add
    -- other operators!
    OpN _ ->
      do c <- case map cClock ts of
                [] -> pure ConstExpr
                t : ss -> do mapM_ (sameClock t) ss
                             pure t
         mapM_ (\t -> subType (cType t) BoolType) ts
         pure CType { cType = BoolType, cClock = c }


-- | Infer the type for a branch of a merge.
inferMergeCase :: Ident -> CType -> MergeCase -> M [Type]
inferMergeCase i it (MergeCase p e) =
  do t <- inferConstExpr p
     subType t (cType it)
     c <- inferExpr e
     let this = KnownClock (WhenClock (range p) p i)
     mapM_ (sameClock this . cClock) c
     pure (map cType c)


-- | Types of unary opertaors.
checkOp1 :: Op1 -> CType -> M CType
checkOp1 op t =
  case op of
    Pre -> pure t

    Current ->
      do c <- clockParent (cClock t)
         pure t { cClock = c }

    Not ->
      do subType (cType t) BoolType
         pure t

    Neg -> do t1 <- classArith1 "-" (cType t)
              pure t { cType = t1 }

    IntCast ->
      do subType (cType t) RealType
         pure t { cType = IntType }

    RealCast ->
      do subType (cType t) IntType
         pure t { cType = RealType }


-- | Types of binary operators.
checkOp2 :: Op2 -> CType -> CType -> M CType
checkOp2 op2 x y =
  do c <- sameClock (cClock x) (cClock y)
     let clocked t = pure CType { cType = t, cClock = c }

         tx = cType x
         ty = cType y

         bool2 = do subType tx BoolType
                    subType ty BoolType
                    clocked BoolType

     case op2 of
       FbyArr   -> typeLUB tx ty >>= clocked
       Fby      -> typeLUB tx ty >>= clocked

       And      -> bool2
       Or       -> bool2
       Xor      -> bool2
       Implies  -> bool2

       Eq       -> classEq tx ty >> clocked BoolType
       Neq      -> classEq tx ty >> clocked BoolType

       Lt       -> classOrd "<"  tx ty >> clocked BoolType
       Leq      -> classOrd "<=" tx ty >> clocked BoolType
       Gt       -> classOrd ">"  tx ty >> clocked BoolType
       Geq      -> classOrd ">=" tx ty >> clocked BoolType

       Add      -> classArith2 "+"   tx ty >>= clocked
       Sub      -> classArith2 "-"   tx ty >>= clocked
       Mul      -> classArith2 "*"   tx ty >>= clocked
       Div      -> classArith2 "/"   tx ty >>= clocked
       Mod      -> classArith2 "mod" tx ty >>= clocked

       Power    -> notYetImplemented "Exponentiation"

       Replicate -> panic "checkOp2" [ "`replicate` should have been checked."]

       Concat ->
         do t1 <- tidyType tx
            t2 <- tidyType ty
            case (t1,t2) of
              (ArrayType elT1 n, ArrayType elT2 m) ->
                do elT <- typeLUB elT1 elT2
                   l   <- addConsts n m
                   clocked (ArrayType elT l)
              _ -> reportError "`|` expects two arrays."



-- | Infer the type of a variable.
inferVar :: Name -> M CType
inferVar x =
  case x of
    Unqual i -> do mb <- lookupIdentMaybe i
                   case mb of
                     Just c  -> pure c
                     Nothing -> inferConstVar x
    Qual {}  -> inferConstVar x

-- | Infer the type for a named constant.
inferConstVar :: Name -> M CType
inferConstVar x =
  inRange (range x) $
  do t <- lookupConst x
     pure CType { cType = t, cClock = ConstExpr }

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
        notYetImplemented "array slices"


checkLHS :: LHS Expression -> M CType
checkLHS lhs =
  case lhs of
    LVar i -> lookupIdent i
    LSelect l s ->
      do t  <- checkLHS l
         t1 <- checkSelector (cType t) s
         pure t { cType = t1 }

checkEquation :: Equation -> M ()
checkEquation eqn =
  case eqn of
    Assert e ->
      do ct <- oneType =<< inferExpr e
         cType ct `subType` BoolType
         -- does clock need to be base?
         -- XXX: maybe make sure that it does not depend on current
         -- values of outputs?  The caller can't really do anything about those.

    Property e ->
      do ct <- oneType =<< inferExpr e
         cType ct `subType` BoolType
         -- does clock need to be base?

    IsMain -> pure ()

    Define ls e ->
      do lts <- mapM checkLHS ls
         rts <- inferExpr e

         let llen = length lts
             rlen = length rts
         unless (llen == rlen) $
            reportError $
            nestedError "Arity mismatch in equation definition:"
              [ "Left-hand-side:" <+> text (show llen) <+> "patterns"
              , "Right-hand-side:" <+> text (show rlen) <+> "values"
              ]

         zipWithM_ subType   (map cType lts)  (map cType rts)
         zipWithM_ sameClock (map cClock lts) (map cClock rts)




--------------------------------------------------------------------------------
-- Comparsions of types

-- | Check if two CTypes are compatible.  If one does not have a clock
-- (e.g., it is a constnat), and the other one does, then result type
-- is the one with the clock.
-- (aak ctypeLUB)
sameCType :: CType -> CType -> M CType
sameCType t1 t2 =
  do t <- typeLUB (cType t1) (cType t2)
     c <- sameClock (cClock t1) (cClock t2)
     pure CType { cType = t, cClock = c }

ctypeLUBs :: CType -> [CType] -> M CType
ctypeLUBs t xs =
  case xs of
    [] -> pure t
    a : as -> do b <- sameCType t a
                 ctypeLUBs b as



sameCTypes :: [CType] -> [CType] -> M [CType]
sameCTypes xs ys =
  case (xs,ys) of
    ([],[])     -> pure []
    (a:as,b:bs) -> (:) <$> sameCType a b <*> sameCTypes as bs
    _ -> reportError "Arity mismatch."


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

       (BoolType,BoolType) -> pure x
       (RealType,RealType) -> pure x
       (NamedType a, NamedType b) | a == b -> pure x
       (ArrayType a b, ArrayType c d) ->
          do sameConsts b d
             elT <- typeLUB a c
             pure (ArrayType elT b)
       _ -> reportError $ text $
                            "Types " ++ showPP x ++ " and " ++ showPP y ++
                            "are not compatible."


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
sameClock :: IClock -> IClock -> M IClock
sameClock x y =
  case (x,y) of
    (ConstExpr,_) -> pure y
    (_,ConstExpr) -> pure x
    (BaseClock,BaseClock) -> pure x
    (KnownClock a, KnownClock b) -> sameKnownClock a b >> pure x
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
clockParent ct =
  case ct of
    BaseClock -> reportError "The base clock has not parent."
    KnownClock (WhenClock _ _ i) -> cClock <$> lookupIdent i
    ConstExpr -> pure ConstExpr

isConstExpr :: IClock -> Bool
isConstExpr c =
  case c of
    ConstExpr -> True
    _         -> False



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
sameConsts = cmpConsts "equal to" (==)

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





