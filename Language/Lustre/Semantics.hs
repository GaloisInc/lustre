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
  , evalConst
  )
  where

import Data.Map(Map)
import qualified Data.Map as Map
import Control.Monad(join)

import Language.Lustre.AST
import Language.Lustre.Semantics.Value
import Language.Lustre.Semantics.BuiltIn


-- | Interpretations of free names.
data Env = Env
  { envConsts   :: Map Name Value
  , envConstFun :: Map Name ([Value] -> EvalM Value)
  , envVars     :: Map Name ReactValue
  , envNodes    :: Map Name ([Value] -> [ReactValue] -> EvalM [ReactValue])
  }




--------------------------------------------------------------------------------



evalConst :: Env -> Expression -> EvalM Value
evalConst env expr =
  case expr of
    ERange _ e -> evalConst env e


    Lit l     -> case l of
                   Int n  -> sInt n
                   Real n -> sReal n
                   Bool n -> sBool n

    IfThenElse b t e ->
      join (sITE <$> evalConst env b <*> evalConst env t <*> evalConst env e)

    WithThenElse be t e ->
      do bv <- evalConst env be
         case bv of
           VNil    -> return VNil
           VBool b -> if b then evalConst env t else evalConst env e
           _       -> typeError "with-then-else" "A `bool`"

    When {}     -> crash "evalConst" "`when` is not a constant expression."
    Merge {}    -> crash "evalConst" "`merge` is not a constant expression."

    Var x ->
      case Map.lookup x (envConsts env) of
        Just v  -> pure v
        Nothing -> crash "evalConst" ("Undefined variable `" ++ show x ++ "`.")

    CallPos fe es ->
      case fe of
        NodeInst fn [] ->
          case Map.lookup fn (envConstFun env) of
            Just f  -> f =<< mapM (evalConst env) es
            Nothing -> crash "evalConst" "Undefined constant function"
        _ -> crash "evalConst" "Constant function with static parameters?"


    Tuple es    -> sTuple =<< mapM (evalConst env) es
    Array es    -> sArray =<< mapM (evalConst env) es
    Struct {}   -> error "[evalConst] XXX: Struct"

    Select e sel ->
      do selF <- evalSel env sel
         selF =<< evalConst env e

    EOp1 op e ->
      do v <- evalConst env e
         case op of
           Not       -> sNot v
           Neg       -> sNeg v
           IntCast   -> sReal2Int v
           RealCast  -> sInt2Real v

           Pre       -> crash "evalConst" "`pre` is not a constant"
           Current   -> crash "evalConst" "`current` is not a constant"

    EOp2 e1 op e2 ->
      do x <- evalConst env e1
         y <- evalConst env e2
         case op of
           Fby     -> crash "evalConst" "`fby` is not a constant"

           And     -> sAnd x y
           Or      -> sOr x y
           Xor     -> sXor x y
           Implies -> sImplies x y

           Eq      -> sEq x y
           Neq     -> sNeq x y

           Lt      -> sLt x y
           Leq     -> sLeq x y
           Gt      -> sGt x y
           Geq     -> sGeq x y

           Mul     -> sMul x y
           Mod     -> sMod x y
           Div     -> sDiv x y
           Add     -> sAdd x y
           Sub     -> sSub x y
           Power   -> sPow x y

           Replicate -> sReplicate x y
           Concat    -> sConcat x y

    EOpN op es ->
      do vs <- mapM (evalConst env) es
         case op of
           AtMostOne -> sBoolRed "at-most-one" 0 1 vs
           Nor       -> sBoolRed "nor" 0 0 vs



evalSel :: Env -> Selector Expression -> EvalM (Value -> EvalM Value)
evalSel env sel =
  case sel of
    SelectField f ->
      pure (sSelectField f)

    SelectElement ei ->
      do i <- evalConst env ei
         pure (sSelectIndex i)

    SelectSlice s   ->
      do start <- evalConst env (arrayStart s)
         end   <- evalConst env (arrayEnd s)
         step  <- mapM (evalConst env) (arrayStep s)
         pure (sSelectSlice ArraySlice { arrayStart = start
                                       , arrayEnd   = end
                                       , arrayStep  = step
                                       })





evalExpr :: Env -> Expression -> EvalM ReactValue
evalExpr env expr =

  case expr of
    ERange _ e -> evalExpr env e

    Lit l ->
      pure $
      case l of
        Int n  -> dInt n
        Real r -> dReal r
        Bool b -> dBool b

    IfThenElse be te ee ->
      do b <- evalExpr env be
         t <- evalExpr env te
         e <- evalExpr env ee
         ite b t e

    WithThenElse be t e ->
      do v <- evalConst env be
         case v of
           VNil    -> pure dNil
           VBool b -> if b then evalExpr env t else evalExpr env e
           _       -> typeError "wte" "a `bool`"

    When {}         -> error "[evalExpr] XXX: When"
    Merge {}        -> error "[evalExpr] XXX: Merge"

    Var x ->
      case Map.lookup x (envVars env) of
        Just r  -> pure r
        Nothing ->
          crash "evalExpr" ("Undefined variable: `" ++ show x ++ "`.")

    CallPos {}      -> error "[evalExpr] XXX: CallPos"

    Tuple es        -> dTuple =<< mapM (evalExpr env) es
    Array es        -> dArray =<< mapM (evalExpr env) es
    Struct {}       -> error "[evalExpr] XXX: Struct"

    Select e sel ->
      do selF <- evalSel env sel
         v    <- evalExpr env e
         selectOp selF v

    EOp1 op e     -> op1 op =<< evalExpr env e
    EOp2 e1 op e2 -> do x <- evalExpr env e1
                        y <- evalExpr env e2
                        op2 op x y
    EOpN op es    -> opN op =<< mapM (evalExpr env) es



