{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Constraint where

import Text.PrettyPrint as PP
import Control.Monad(unless)
import Data.Maybe(catMaybes)

import Language.Lustre.AST
import Language.Lustre.TypeCheck.Monad
import Language.Lustre.Pretty
import Language.Lustre.Panic

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

      Arith1 op a b   -> opError op [a] [b]
      Arith2 op a b c -> opError op [a,b] [c]
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
       Arith1 op a b    -> classArith1 op a b
       Arith2 op a b c  -> classArith2 op a b c
       CmpEq op a b     -> classEq op a b
       CmpOrd op a b    -> classOrd op a b


classArith1 :: Doc -> Type -> Type -> M Bool
classArith1 op s0 t0 =
  do t <- tidyType t0
     case t of
       IntType  -> subType s0 IntType >> pure True
       RealType -> subType s0 RealType >> pure True
       TVar {} ->
         do s <- tidyType s0
            case s of
              IntType         -> subType IntType t0 >> pure True
              IntSubrange {}  -> subType IntType t0 >> pure True
              RealType        -> subType RealType t0 >> pure True
              TVar {}         -> addConstraint (Arith1 op s0 t) >> pure False
              _               -> typeError
       _ -> typeError
  where
  typeError = reportError (opError op [s0] [t0])


-- | Can we do binary arithemtic on this type, and if so what's the
-- type of the answer.
classArith2 :: Doc -> Type -> Type -> Type -> M Bool
classArith2 op s0 t0 r0 =
  do r <- tidyType r0
     case r of
       IntType  -> subType s0 IntType  >> subType t0 IntType >> pure True
       RealType -> subType s0 RealType >> subType t0 RealType >> pure True
       TVar {}  ->
         do s <- tidyType s0
            case s of
              IntType  -> subType t0 IntType  >> subType IntType r >> pure True
              IntSubrange {} ->
                subType t0 IntType >> subType IntType r >> pure True
              RealType -> subType t0 RealType >> subType RealType r >> pure True
              TVar {} ->
                do t <- tidyType t0
                   case t of
                     IntType  ->
                        subType s0 IntType  >> subType IntType r >> pure True
                     IntSubrange {} ->
                        subType t0 IntType >> subType IntType r >> pure True
                     RealType ->
                        subType s0 RealType >> subType RealType r >> pure True
                     TVar {} -> addConstraint (Arith2 op s t r) >> pure False
                     _ -> typeError
              _ -> typeError
       _ -> typeError

  where
  typeError = reportError (opError op [s0,t0] [r0])






-- | Are these types comparable of equality
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



-- Subtype is like "subset"
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
            _    <- subType elT elT'
            _    <- sameType (ArrayType elT' n) y
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
                   _    <- subType elT' elT
                   sameType s (ArrayType elT' sz)
                   pure True
              IntType        -> addConstraint (Subtype s t) >> pure False
              IntSubrange {} -> addConstraint (Subtype s t) >> pure False
              TVar {}        -> addConstraint (Subtype s t) >> pure False

       _ -> sameType s y >> pure True

--------------------------------------------------------------------------------

intConst :: Expression -> M Integer
intConst x =
  case x of
    ERange _ y  -> intConst y
    Lit (Int a) -> pure a
    _ -> reportError $ nestedError
           "Constant expression is not a concrete integer."
           [ "Expression:" <+> pp x ]


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
leqConsts e1 e2 =
  do x <- intConst e1
     y <- intConst e2
     unless (x <= y) $ reportError
                     $ pp x <+> "is not less-than, or equal to" <+> pp y


