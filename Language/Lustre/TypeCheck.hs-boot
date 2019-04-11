module Language.Lustre.TypeCheck where

import Language.Lustre.AST(Expression,CType,Type,IClock)
import Language.Lustre.TypeCheck.Monad(M)

inferExpr       :: Expression -> M (Expression,[CType])
inferExpr1      :: Expression -> M (Expression,CType)
checkConstExpr  :: Expression -> Type -> M Expression
checkExpr1      :: Expression -> Type -> M (Expression, IClock)

