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


opError :: Doc -> [Type] -> Doc
opError op ins =
  nestedError "Failed to check that that the types support operation."
              (("Operation:" <+> op) : tys "Input" ins)
  where
  tys lab ts = [ lab <+> integer n PP.<> ":" <+> pp t
                      | (n,t) <- [ 1 .. ] `zip` ts ]

-- | Compute the least upper bound of two types.
tLUB :: Type -> Type -> M Type
tLUB t1 t2 =
 case t1 of

   BoolType ->
     do subType t2 t1
        pure t1

   RealType ->
    do subType t2 t1
       pure t1

   IntType ->
    do subType t2 t1
       pure t1

   NamedType _ ->
    do subType t2 t1
       pure t1

   ArrayType elT1 sz1 ->
     case t2 of
       ArrayType elT2 sz2 ->
         do sameConsts sz1 sz2
            t <- tLUB elT1 elT2
            pure (ArrayType t sz1)
       _ -> err

   IntSubrange l1 h1 ->
     case t2 of
       IntType -> pure t2
       IntSubrange l2 h2 ->
         do (l3,h3) <- intervalUnion (l1,h1) (l2,h2)
            pure (IntSubrange l3 h3)
       _ -> err

   TypeRange {} -> panic "tLUB" [ "Unexpected `TypeRange`." ]

  where
  err = reportError (opError "find common type" [ t1, t2 ])


-- | Computes the type of the result of a unariy arithmetic operator.
tArith1 :: SourceRange -> Op1 -> Type -> M Type
tArith1 r op t =
  case t of
    IntType  -> pure IntType
    RealType -> pure RealType
    IntSubrange l h ->
      do (l1,h1) <- intervalFor1 r op (l,h)
         pure (IntSubrange l1 h1)
    _ -> reportError (opError (pp op) [t])


-- | Computes the type of the result of a binary arithmetic operator.
tArith2 :: SourceRange -> Op2 -> Type -> Type -> M Type
tArith2 r op t1 t2 =
  case t1 of
    IntType  -> subType t2 t1       >> pure t1
    RealType -> subType t2 RealType >> pure t1

    IntSubrange l1 h1 ->
      case t2 of
        IntType -> pure t2
        IntSubrange l2 h2 ->
          do (l3,h3) <- intervalFor2 r op (l1,h1) (l2,h2)
             pure (IntSubrange l3 h3)
        _ -> err

    _ -> err

  where
  err = reportError (opError (pp op) [t1,t2])



-- | Checks that the given types can be compared for equality.
classEq :: Doc -> Type -> Type -> M ()
classEq _op s t =
  do _ <- tLUB s t   -- we can compare values of any comparable type.
                     -- XXX: Perhaps it is useful to save the common type?
     pure ()


-- | Are these types comparable for ordering
classOrd :: Doc -> Type -> Type -> M ()
classOrd op s t =
  do r <- tLUB s t
     case r of
       IntType        -> pure ()
       IntSubrange {} -> pure ()
       RealType       -> pure ()
       _ -> reportError (opError op [s,t])


-- | Subtype is like "subset" (i.e., we want to make sure that all values
-- of the first type are also good values for the second type).
subType :: Type -> Type -> M ()
subType s t =
  case (s,t) of
    (IntSubrange {},  IntType) -> pure ()
    (IntSubrange a b, IntSubrange c d) -> leqConsts c a >> leqConsts b d

    (ArrayType elT1 sz1, ArrayType elT2 sz2) ->
      do sameConsts sz1 sz2
         subType elT1 elT2

    (IntType,IntType)   -> pure ()
    (RealType,RealType) -> pure ()
    (BoolType,BoolType) -> pure ()
    (NamedType x, NamedType y) | x == y -> pure ()
    _ -> reportError $ nestedError
          "Type mismatch:"
          [ "Values of type:" <+> pp s
          , "Do not fit into type:" <+> pp t
          ]




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


