-- | Additional reading:
-- * http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
-- * https://inst.eecs.berkeley.edu/~ee249/fa07/lecture-lustre-trans.pdf
-- * http://www.cse.unsw.edu.au/~plaice/archive/JAP/P-NYAS92-lustreSemantics.pdf
module Language.Lustre.Semantics
  ( Value(..)
  , EvalM
  , Error
  , ReactValue
  , Step(..)
  , Env(..)
  , evalExpr
  )
  where

import Data.Map(Map)

import Language.Lustre.AST
import Language.Lustre.Semantics.Stream
import Language.Lustre.Semantics.Value
import Language.Lustre.Semantics.BuiltIn


-- | Interpretations of free names.
data Env = Env
  { envConsts   :: Map Name Value
  , envVars     :: Map Name ReactValue
  , envNodes    :: Map Name ([ReactValue] -> EvalM [ReactValue])
  }




--------------------------------------------------------------------------------


evalLiteral :: Literal -> ReactValue
evalLiteral l = case l of
                  Int n  -> dInt n
                  Real r -> dReal r
                  Bool b -> dBool b


evalConst :: Env -> Expression -> EvalM Value
evalConst = undefined

evalExpr :: Env -> Expression -> ReactValue
evalExpr env expr =

  case expr of
    ERange _ e -> evalExpr env e

    Lit l -> evalLiteral l

    IfThenElse b t e -> ite (evalExpr env b) (evalExpr env t) (evalExpr env e)

    WithThenElse be t e ->
      Eff $ do v <- evalConst env be
               case v of
                 VNil    -> pure dNil
                 VBool b -> pure (if b then evalExpr env t else evalExpr env e)
                 _       -> typeError "wte" "a `bool`"

    When {}         -> error "[evalExpr] XXX: When"
    Merge {}        -> error "[evalExpr] XXX: Merge"
    Var {}          -> error "[evalExpr] XXX: Var"
    CallPos {}      -> error "[evalExpr] XXX: CallPos"

    Tuple es        -> dTuple (map (evalExpr env) es)
    Array es        -> dArray (map (evalExpr env) es)
    Struct {}       -> error "[evalExpr] XXX: Struct"

    Select e sel -> selectOp evalSel (evalExpr env e)
      where evalSel = case sel of
                        SelectField f -> SelectField f
                        SelectElement i -> SelectElement (evalExpr env i)
                        SelectSlice s -> SelectSlice
                          ArraySlice { arrayStart = evalExpr env (arrayStart s)
                                     , arrayEnd   = evalExpr env (arrayEnd s)
                                     , arrayStep  = evalExpr env <$> arrayStep s
                                     }

    EOpN op es    -> opN op (map (evalExpr env) es)
    EOp1 op e     -> op1 op (evalExpr env e)
    EOp2 e1 op e2 -> op2 op (evalExpr env e1) (evalExpr env e2)




