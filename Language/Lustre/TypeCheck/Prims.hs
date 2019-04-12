{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Prims ( inferPrim ) where

import Data.Traversable(for)
import Data.Foldable(for_)
import Text.PrettyPrint
import Control.Monad(unless,zipWithM)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.TypeCheck.Monad
import Language.Lustre.TypeCheck.Constraint
import {-# SOURCE #-} Language.Lustre.TypeCheck
import Language.Lustre.TypeCheck.Utils


-- | Infer the type of a call to a primitive node.
inferPrim ::
  SourceRange   {- ^ Location of operator -} ->
  PrimNode      {- ^ Operator -} ->
  [StaticArg]   {- ^ Static arguments -} ->
  [Expression]  {- ^ Normal argumetns -} ->
  M (Expression,[CType])
inferPrim r prim as es =
  case prim of

    Iter {} -> notYetImplemented "iterators."

    Op1 op ->
      case es of
        [e] -> noStatic op >> inferOp1 r op e
        _   -> reportError (pp op <+> "expects 1 argument.")

    Op2 op ->
      case es of
        [e1,e2] -> noStatic op >> inferOp2 r op e1 e2
        _ -> reportError (pp op <+> "expects 2 arguments.")

    ITE ->
      case es of
        [e1,e2,e3] -> noStatic ITE >> inferITE r e1 e2 e3
        _ -> reportError "`if-then-else` expects 3 arguments."


    OpN op -> noStatic op >> inferOpN r op es
  where
  noStatic op =
    unless (null as) $
    reportError (backticks (pp op) <+> "does not take static arguments")


-- | Check an if-then-else expression.
inferITE :: SourceRange -> Expression -> Expression -> Expression ->
                                                        M (Expression,[CType])
inferITE r e1 e2 e3 =
  do (e1',c) <- checkExpr1 e1 BoolType
     (e2',ctTHEN) <- inferExpr e2
     (e3',ctELSE) <- inferExpr e3
     sameLen ctTHEN ctELSE
     for_ ctTHEN (sameClock c . cClock)
     for_ ctELSE (sameClock c . cClock)
     ts <- zipWithM tLUB (map cType ctTHEN) (map cType ctELSE)
     let cts = [ CType { cClock = c, cType = t } | t <- ts ]
     pure (eITE r e1' e2' e3', cts)



-- | Check a @current@ expression.
inferCurrent :: Expression -> M (Expression,[CType])
inferCurrent e =
  do checkTemporalOk "current"
     (e',ctsIn) <- inferExpr e
     cts <- for ctsIn $ \ct -> do c <- clockParent (cClock ct)
                                  pure ct { cClock = c }
     pure (e',cts)


-- | Check a uniary operator.
inferOp1 :: SourceRange -> Op1 -> Expression -> M (Expression,[CType])
inferOp1 r op e =
  do (a, ct) <- check
     pure (eOp1 r op a, ct)

  where
  check =
    case op of

      Pre ->
        do checkTemporalOk "pre"
           inferExpr e

      Current -> inferCurrent e

      Not ->
        do (e', i) <- checkExpr1 e BoolType
           let ct = CType { cType = BoolType, cClock = i }
           pure (e', [ct])

      Neg ->
        do (e', ct0) <- inferExpr1 e
           t <- tArith1 r op (cType ct0)
           let ct = CType { cClock = cClock ct0, cType = t }
           pure (e', [ct])

      IntCast ->
        do (e', i) <- checkExpr1 e RealType
           let ct = CType { cType = IntType, cClock = i }
           pure (e', [ct])

      FloorCast ->
        do (e', i) <- checkExpr1 e RealType
           let ct = CType { cType = IntType, cClock = i }
           pure (e', [ct])

      RealCast ->
        do (e', i) <- checkExpr1 e IntType
           let ct = CType { cType = RealType, cClock = i }
           pure (e', [ct])


-- | Types of binary operators.
inferOp2 ::
  SourceRange -> Op2 -> Expression -> Expression -> M (Expression,[CType])
inferOp2 r op2 e1 e2 =
  do (a, b, cts) <- check
     pure (eOp2 r op2 a b, cts)

  where
  check =
    case op2 of
      FbyArr -> inferFBY "->"
      Fby    -> inferFBY "fby"

      CurrentWith ->
        do checkTemporalOk "currentWith"
           (a,ctDEF) <- inferExpr e1
           (b,ctEXP) <- inferCurrent e2
           sameLen ctDEF ctEXP
           cts <- zipWithM ctLUB ctDEF ctEXP
           pure (a, b, cts)

      Replicate ->
        do (a,ctE) <- inferExpr1 e1
           b       <- checkConstExpr e2 IntType
           let ct = ctE { cType = ArrayType (cType ctE) b }
           pure (a, b, [ct])

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

      Add      -> arith Add
      Sub      -> arith Sub
      Mul      -> arith Mul
      Div      -> arith Div
      Mod      -> arith Mod

      Power    -> notYetImplemented "Exponentiation"
      Concat   -> inferConcat


  inferFBY x =
    do checkTemporalOk x
       (a,cts1) <- inferExpr e1
       (b,cts2) <- inferExpr e2
       sameLen cts1 cts2
       ct <- zipWithM ctLUB cts1 cts2
       pure (a, b, ct)


  infer2    = do (a,t1) <- inferExpr1 e1
                 (b,t2) <- inferExpr1 e2
                 sameClock (cClock t1) (cClock t2)
                 pure (cClock t1, cType t1, cType t2, a, b)

  bool2     = do (c,t1,t2,a,b) <- infer2
                 _ <- subType t1 BoolType
                 _ <- subType t2 BoolType
                 let ct = CType { cType = BoolType, cClock = c }
                 pure (a, b, [ct])

  ordRel op = do (c,t1,t2,a,b) <- infer2
                 _ <- classOrd op t1 t2
                 let ct = CType { cType = BoolType, cClock = c }
                 pure (a, b, [ct])

  arith x   = do (c,t1,t2,a,b) <- infer2
                 ty <- tArith2 r x t1 t2
                 let ct = CType { cType = ty, cClock = c }
                 pure (a, b, [ct])

  eqRel op  = do (a,cts1) <- inferExpr e1
                 (b,cts2) <- inferExpr e2
                 sameLen cts1 cts2
                 for_ (zip cts1 cts2) $ \(ct1,ct2) ->
                   do sameClock (cClock ct1) (cClock ct2)
                      classEq op (cType ct1) (cType ct2)
                 i <- case cts1 of
                        [] -> newClockVar
                        ct : _ -> pure (cClock ct)
                 let ct = CType { cType = BoolType, cClock = i }
                 pure (a, b, [ct])

  inferConcat =
    do (a, ct1) <- inferExpr1 e1
       (b, ct2) <- inferExpr1 e2
       sameClock (cClock ct1) (cClock ct2)
       t1 <- tidyType (cType ct1)
       t2 <- tidyType (cType ct2)
       case t1 of
         ArrayType elT1 sz1 ->
           case t2 of
             ArrayType elT2 sz2 ->
               do t  <- tLUB elT1 elT2
                  sz <- addExprs sz1 sz2
                  let ct = CType { cType = ArrayType t sz, cClock = cClock ct1 }
                  pure (a,b,[ct])
             _       -> typeError "right" t2
         _ -> typeError "left" t1
    where

    typeError x t = reportError $ nestedError
                      ("Incorrect" <+> x <+> "argument to `|`")
                      [ "Expected:" <+> "array"
                      , "Actual type:" <+> pp t ]


-- | Check a variable arity operator.
inferOpN :: SourceRange -> OpN -> [Expression] -> M (Expression,[CType])
inferOpN r op es =
  case op of
    AtMostOne -> boolOp
    Nor       -> boolOp
  where
  boolOp =
    do (es',cts) <- unzip <$> for es inferExpr1
       i <- newClockVar
       for_ cts (sameClock i . cClock)
       let ct = CType { cClock = i, cType = BoolType }
       pure (eOpN r op es',[ct])



