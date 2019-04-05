module Language.Lustre.TypeCheck where

import Language.Lustre.AST(Expression,CType)
import Language.Lustre.TypeCheck.Monad(M)

checkExpr  :: Expression -> [CType] -> M Expression
checkExpr1 :: Expression -> CType -> M Expression

