{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Prims ( checkPrim ) where

import Data.Traversable(for)
import Text.PrettyPrint
import Control.Monad(zipWithM_,replicateM,unless)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic(panic)
import Language.Lustre.TypeCheck.Monad
import Language.Lustre.TypeCheck.Arity
import Language.Lustre.TypeCheck.Constraint
import {-# SOURCE #-} Language.Lustre.TypeCheck
import Language.Lustre.TypeCheck.Utils


-- | Infer the type of a call to a primitive node.
checkPrim ::
  SourceRange   {- ^ Location of operator -} ->
  PrimNode      {- ^ Operator -} ->
  [StaticArg]   {- ^ Static arguments -} ->
  [Expression]  {- ^ Normal argumetns -} ->
  [CType]       {- ^ Expected result -} ->
  M Expression
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



-- | Check the argument to a "current" expression.
checkCurrent :: Expression -> [CType] -> M Expression
checkCurrent e tys =
  do checkTemporalOk "current"
     tys1 <- for tys $ \ty ->
                do c <- newClockVar
                   pure ty { cClock = c }
     e1 <- checkExpr e tys1

     -- By now we should have figured out the missing clock,
     -- so check straight away
     zipWithM_ checkClock tys tys1
     pure e1

  where
  checkClock ty newTy = sameClock (cClock ty) =<< clockParent (cClock newTy)



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
           ensure (Arith1 Neg t (cType ty))
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





