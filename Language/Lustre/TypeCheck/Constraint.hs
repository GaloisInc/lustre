{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Constraint where

import Text.PrettyPrint as PP
import Control.Monad(unless)
import Data.Maybe(catMaybes)

import Language.Lustre.AST
import Language.Lustre.TypeCheck.Monad
import qualified Language.Lustre.Semantics.Const as C
import Language.Lustre.Pretty
import Language.Lustre.Semantics.BuiltIn(eucledean_div_mod)
import Language.Lustre.Panic


-- | Compute the least upper bound of two types.
tLUB :: Type -> Type -> M Type
tLUB t1 t2 =
  do t1' <- tidyType t1
     t2' <- tidyType t2
     let err  = reportError
                   (nestedError "Incompatible types:" [ pp t1', pp t2' ])
         tvar = reportError "XXX: Type variable"
     case t1' of

       BoolType ->
         do _ <- subType t2' t1'
            pure t1'

       RealType ->
        do _ <- subType t2' t1'
           pure t1'

       IntType ->
        do _ <- subType t2' t1'
           pure t1'

       NamedType _ ->
        do _ <- subType t2' t1'
           pure t1'

       ArrayType elT1 sz1 ->
         case t2' of
           ArrayType elT2 sz2 ->
             do sameConsts sz1 sz2
                t <- tLUB elT1 elT2
                pure (ArrayType t sz1)
           TVar {} -> tvar
           _ -> err

       IntSubrange l1 h1 ->
         case t2' of
           IntType -> pure t2'
           IntSubrange l2 h2 ->
             do (l3,h3) <- intervalUnion (l1,h1) (l2,h2)
                pure (IntSubrange l3 h3)
           TVar {} -> tvar
           _ -> err

       TypeRange {} -> panic "tLUB" ["Unexpected type range"]

       TVar {} -> tvar



-- Quick and dirty "defaulting" for left-over typing constraints.
-- To do this properly, we should keep lower and upper bounds on variables.
solveConstraints :: M ()
solveConstraints =
  do cs1 <- resetConstraints
     cs2 <- repeated upToInt cs1
     cs3 <- repeated atMostInt cs2
     progress <- mapM solveConstraint cs3
     if or progress
       then solveConstraints
       else do unsolved <- resetConstraints
               mapM_ typeError unsolved
  where
  repeated p xs =
    do res <- mapM p xs
       case sequence res of
         Nothing -> repeated p (catMaybes res)
         Just ys -> pure ys

  upToInt (r,c) =
    inRangeSetMaybe r $
    do c1 <- tidyConstraint c
       case c1 of
         Subtype (IntSubrange {}) (TVar x) -> bindTVar x IntType >> pure Nothing
         _ -> pure (Just (r,c1))

  atMostInt (r,c) =
    inRangeSetMaybe r $
    do c1 <- tidyConstraint c
       case c1 of
         Subtype (TVar x) IntType -> bindTVar x IntType >> pure Nothing
         _ -> pure (Just (r,c1))

  typeError (r,ctr) =
    inRangeSetMaybe r $ reportError $
     case ctr of
      Subtype a b -> nestedError
                        "Failed to show that"
                        [ "Type:" <+> pp a
                        , "Fits in:" <+> pp b]

      CmpEq op a b    -> opError op [a,b] []
      CmpOrd op a b   -> opError op [a,b] []


opError :: Doc -> [Type] -> [Type] -> Doc
opError op ins outs =
  nestedError "Failed to check that that the types support operation."
    (("Operation:" <+> op) : (tys "Input" ins ++ tys "Output" outs))
  where
  tys lab ts = [ lab <+> integer n PP.<> ":" <+> pp t
                      | (n,t) <- [ 1 .. ] `zip` ts ]


ensure :: Constraint -> M ()
ensure c =
  do _ <- solveConstraint (Nothing, c)
     pure ()

solveConstraint :: (Maybe SourceRange,Constraint) -> M Bool
solveConstraint (r,ctr) =
  inRangeSetMaybe r $
  do ctr1 <- tidyConstraint ctr
     case ctr1 of
       Subtype a b      -> subType a b
       CmpEq op a b     -> classEq op a b
       CmpOrd op a b    -> classOrd op a b


-- | Computes the type of the result of a unariy arithmetic operator.
tArith1 :: SourceRange -> Op1 -> Type -> M Type
tArith1 r op t =
  do t' <- tidyType t
     let err = reportError
                ("Type" PP.<> pp t <+> "does not support unary" <+> pp op)
         tvar = reportError "XXX: TVar"
     case t' of
       IntType  -> pure IntType
       RealType -> pure RealType
       IntSubrange l h ->
         do (l1,h1) <- intervalFor1 r op (l,h)
            pure (IntSubrange l1 h1)
       TVar {} -> tvar
       _ -> err

-- | Computes the type of the result of a binary arithmetic operator.
tArith2 :: SourceRange -> Op2 -> Type -> Type -> M Type
tArith2 r op t1 t2 =
  do t1' <- tidyType t1
     t2' <- tidyType t2
     let err = reportError $ nestedError
               ("Operation" <+> pp op <+> "is not supported on types:")
               [ pp t1', pp t2' ]
         tvar = reportError "XXX: TVAR"

     case t1' of
       IntType  -> subType t2' IntType  >> pure t1'
       RealType -> subType t2' RealType >> pure t1'

       IntSubrange l1 h1 ->
         case t2' of
           IntType -> pure t2'
           IntSubrange l2 h2 ->
             do (l3,h3) <- intervalFor2 r op (l1,h1) (l2,h2)
                pure (IntSubrange l3 h3)
           TVar {} -> tvar
           _ -> err

       TVar {} -> tvar
       _       -> err





-- | Checks that the given types can be compared for equality.
classEq :: Doc -> Type -> Type -> M Bool
classEq op s0 t0 =
  do s <- tidyType s0
     case s of
       IntSubrange {} -> subType t0 IntType >> pure True
       ArrayType elT sz ->
         do elT' <- newTVar
            _    <- subType t0 (ArrayType elT' sz)
            _    <- classEq op elT elT'
            pure True

       TVar {} ->
         do t <- tidyType t0
            case t of
              IntSubrange {} -> subType s IntType >> pure True
              _              -> subType s t >> pure True
       _ -> subType t0 s >> pure True



-- | Are these types comparable for ordering
classOrd :: Doc -> Type -> Type -> M Bool
classOrd op s' t' =
  do s <- tidyType s'
     case s of
       IntType        -> subType t' IntType >> pure True
       IntSubrange {} -> subType t' IntType >> pure True
       RealType       -> subType t' RealType >> pure True
       TVar {} ->
         do t <- tidyType t'
            case t of
              IntType        -> subType s IntType >> pure True
              IntSubrange {} -> subType s IntType >> pure True
              RealType       -> subType s RealType >> pure True
              TVar {}        -> addConstraint (CmpOrd op s t) >> pure False
              _ -> typeError
       _ -> typeError
  where
  typeError = reportError (opError op [s',t'] [])


sameType :: Type -> Type -> M ()
sameType x y =
  do s <- tidyType x
     t <- tidyType y
     case (s,t) of
      (TVar v, _) -> bindTVar v t
      (_,TVar v)  -> bindTVar v s
      (NamedType a,   NamedType b)   | a == b -> pure ()
      (ArrayType a m, ArrayType b n) -> sameConsts m n >> sameType a b

      (IntType,IntType)   -> pure ()
      (RealType,RealType) -> pure ()
      (BoolType,BoolType) -> pure ()
      (IntSubrange a b, IntSubrange c d) ->
        sameConsts a c >> sameConsts b d
      _ -> reportError $ nestedError
            "Type mismatch:"
            [ "Values of type:" <+> pp s
            , "Do not fit into type:" <+> pp t
            ]



-- | Subtype is like "subset".
-- Returns 'True' if the constraint was solved (possibly generating
-- new sub-constraints).  `False` means that we failed to solved the
-- constraint and instead it was stored to be solved later.
subType :: Type -> Type -> M Bool
subType x y =
  do s <- tidyType x
     case s of
       IntSubrange a b ->
         do t <- tidyType y
            case t of
              IntType         -> pure True
              IntSubrange c d -> leqConsts c a >> leqConsts b d >> pure True
              TVar {}         -> addConstraint (Subtype s t) >> pure False
              _               -> sameType s t >> pure True

       ArrayType elT n ->
         do elT' <- newTVar
            _    <- sameType (ArrayType elT' n) y
            _    <- subType elT elT'
            pure True

       TVar {} ->
         do t <- tidyType y
            case t of
              TypeRange {} -> panic "subType"
                                      ["`tidyType` returned `TypeRange`"]
              RealType     -> sameType s t >> pure True
              BoolType     -> sameType s t >> pure True
              NamedType {} -> sameType s t >> pure True
              ArrayType elT sz ->
                do elT' <- newTVar
                   sameType s (ArrayType elT' sz)
                   _    <- subType elT' elT
                   pure True
              IntType        -> addConstraint (Subtype s t) >> pure False
              IntSubrange {} -> addConstraint (Subtype s t) >> pure False
              TVar {}        -> addConstraint (Subtype s t) >> pure False

       _ -> sameType s y >> pure True

--------------------------------------------------------------------------------


-- XXX: This is temporary.  Eventually, we should make proper constraints,
-- and either try to solve them statically, or just generate them for the
-- checker to verify on each step.


evConstExpr :: Expression -> Maybe C.Value
evConstExpr expr =
  case C.evalConst C.emptyEnv expr of
    Left _ -> Nothing
    Right v -> Just v

normConstExpr :: Expression -> Expression
normConstExpr expr =
  case evConstExpr expr of
    Nothing -> expr
    Just v -> C.valToExpr v

intConst :: Expression -> M Integer
intConst e =
  case evConstExpr e of
    Just (C.VInt a) -> pure a
    _ -> reportError $ nestedError
           "Constant expression is not a concrete integer."
           [ "Expression:" <+> pp e ]

intInterval :: (Expression,Expression) -> M (Integer,Integer)
intInterval (l,h) =
  do i <- intConst l
     j <- intConst h
     pure (i,j)

fromIntInterval :: (Integer,Integer) -> M (Expression,Expression)
fromIntInterval (l,h) = pure (Lit (Int l), Lit (Int h))



sameConsts :: Expression -> Expression -> M ()
sameConsts e1 e2 =
  case (e1,e2) of
    (ERange _ x,_)  -> sameConsts x e2
    (_, ERange _ x) -> sameConsts e1 x
    (Const x _, _)  -> sameConsts x e2
    (_, Const x _)  -> sameConsts e1 x
    (Var x, Var y) | x == y -> pure ()
    _ | x <- evConstExpr e1
      , y <- evConstExpr e2
      , x == y -> pure ()

    _ -> reportError $ nestedError
           "Constants do not match"
           [ "Constant 1:" <+> pp e1
           , "Constant 2:" <+> pp e2
           ]

leqConsts :: Expression -> Expression -> M ()
leqConsts e1 e2 =
  do x <- intConst e1
     y <- intConst e2
     unless (x <= y) $ reportError
                     $ pp x <+> "is not less-than, or equal to" <+> pp y



intervalFor1 :: SourceRange -> Op1 ->
                (Expression,Expression) ->
              M (Expression,Expression)
intervalFor1 _ op i =
  do (l,h) <- intInterval i
     case op of
       Neg -> fromIntInterval (negate h, negate l)
       _ -> panic "intervalFor1" [ "Unexpected unary arithmetic operator"
                                 , showPP op ]


intervalFor2 :: SourceRange -> Op2 ->
               (Expression,Expression) ->
               (Expression,Expression) ->
             M (Expression,Expression)
intervalFor2 _ op i j =
  do u@(l1,h1) <- intInterval i
     v@(l2,h2) <- intInterval j
     case op of
       Add -> fromIntInterval (l1 + l2, h1 + h2)
       Sub -> fromIntInterval (l1 - h2, h1 - l2)
       Mul -> byCases u v $ \a b -> Just (a * b)
       Div -> byCases u v $ \a b -> fst <$> eucledean_div_mod a b
       Mod -> byCases u v $ \a b -> snd <$> eucledean_div_mod a b
       _ -> panic "intervalFor2" [ "Unexpected binary arithmetic operator"
                                 , showPP op ]
  where
  byCases (a,b) (x,y) f =
    case catMaybes [f a x,f a y, f b x, f b y] of
      [] -> reportError ("Invalid call to" <+> pp op)
      ch -> fromIntInterval (minimum ch, maximum ch)

intervalUnion :: (Expression,Expression) ->
                 (Expression,Expression) ->
               M (Expression,Expression)
intervalUnion i j =
  do (l1,h1) <- intInterval i
     (l2,h2) <- intInterval j
     fromIntInterval (min l1 l2, max h1 h2)


