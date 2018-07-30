module Language.Lustre.Semantics.Expression
  ( evalMultiExpr, evalExpr, evalExprs
  , evalMultiConst, evalConst, evalConsts
  )
  where

import qualified Data.Map as Map
import Control.Monad(join)

import Language.Lustre.AST
import Language.Lustre.Semantics.Value
import Language.Lustre.Semantics.Env
import Language.Lustre.Semantics.BuiltIn


-- | Evaluate a static expression, corresponding to a single value.
-- If the expression results in no, or multiple values, then we raise
-- a type error.
evalConst :: Env -> Expression -> EvalM Value
evalConst env expr =
  do vs <- evalMultiConst env expr
     case vs of
       [v] -> pure v
       _   -> typeError "evalConst" "a single value."

-- | Evaluate multiple static expressions and combine multi-values together.
evalConsts :: Env -> [Expression] -> EvalM [Value]
evalConsts env es = concat <$> mapM (evalMultiConst env) es

-- | Evaluate a single static expression, potentially resulting in
-- multiple values.
evalMultiConst :: Env -> Expression -> EvalM [Value]
evalMultiConst env expr =
  case expr of

    ERange _ e -> evalMultiConst env e

    Lit l ->
      one $
      case l of
        Int n  -> sInt n
        Real n -> sReal n
        Bool n -> sBool n

    IfThenElse b t e ->
      one $
      join $ sITE <$> evalConst env b <*> evalConst env t <*> evalConst env e

    WithThenElse be t e ->
      do bv <- evalConst env be
         case bv of
           VBool b -> if b then evalMultiConst env t else evalMultiConst env e
           _       -> typeError "with-then-else" "A `bool`"

    When {}     -> crash "evalMultiConst" "`when` is not a constant expression."
    Merge {}    -> crash "evalMultiConst" "`merge` is not a constant expression."
    Var x ->
      one $
      case Map.lookup x (envConsts env) of
        Just v  -> pure v
        Nothing -> crash "evalMultiConst"
                              ("Undefined variable `" ++ show x ++ "`.")

    CallPos fe es ->
      case fe of
        NodeInst fn [] ->
          case Map.lookup fn (envConstFun env) of
            Just f  -> f =<< evalConsts env es
            Nothing -> crash "evalMultiConst" "Undefined constant function"
        _ -> crash "evalMultiConst" "Constant function with static parameters?"


    Tuple es -> evalConsts env es

    Array es ->
      one $
      sArray =<< mapM (evalConst env) es

    Struct {} -> error "[evalMultiConst] XXX: Struct"

    Select e sel ->
      one $
      do selF <- evalSel env sel
         selF =<< evalConst env e

    EOp1 op e ->
      one $
      do v <- evalConst env e
         case op of
           Not       -> sNot v
           Neg       -> sNeg v
           IntCast   -> sReal2Int v
           RealCast  -> sInt2Real v

           Pre       -> crash "evalMultiConst" "`pre` is not a constant"
           Current   -> crash "evalMultiConst" "`current` is not a constant"

    EOp2 e1 op e2 ->
      one $
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
      one $
      do vs <- evalConsts env es
         case op of
           AtMostOne -> sBoolRed "at-most-one" 0 1 vs
           Nor       -> sBoolRed "nor" 0 0 vs


-- | Evaluate a selector.
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



-- | Evaluate an expression to a single reactive value.
-- It is a type error if the expression evalutes to no, or multiple, values.
evalExpr :: Env -> Expression -> EvalM ReactValue
evalExpr env expr =
  do vs <- evalMultiExpr env expr
     case vs of
       [v] -> pure v
       _   -> typeError "evalExpr" "exactly one result"

-- | Evaluate multiple expressions, and join together multi-values.
evalExprs :: Env -> [Expression] -> EvalM [ReactValue]
evalExprs env es = concat <$> mapM (evalMultiExpr env) es


-- | Evaluate an expression, which may result in multiple values.
evalMultiExpr :: Env -> Expression -> EvalM [ ReactValue ]
evalMultiExpr env expr =

  case expr of
    ERange _ e -> evalMultiExpr env e

    Lit l ->
      one $
      pure $
      case l of
        Int n  -> dInt n
        Real r -> dReal r
        Bool b -> dBool b

    IfThenElse be te ee ->
      one $
      do b <- evalExpr env be
         t <- evalExpr env te
         e <- evalExpr env ee
         ite b t e

    WithThenElse be t e ->
      do v <- evalConst env be
         case v of
           VBool b -> if b then evalMultiExpr env t else evalMultiExpr env e
           _       -> typeError "with-then-else" "a `bool`"

    When {}         -> error "[evalMultiExpr] XXX: When"
    Merge {}        -> error "[evalMultiExpr] XXX: Merge"

    Var x ->
      one $
      case Map.lookup x (envVars env) of
        Just r  -> pure r
        Nothing ->
          crash "evalMultiExpr" ("Undefined variable: `" ++ show x ++ "`.")

    CallPos ni es ->
      do f  <- resolveInstance env ni
         f =<< evalExprs env es

    Tuple es -> evalExprs env es

    Array es ->
      one $
      dArray =<< mapM (evalExpr env) es

    Struct {} -> error "[evalMultiExpr] XXX: Struct"

    Select e sel ->
      one $
      do selF <- evalSel env sel
         v    <- evalExpr env e
         selectOp selF v

    EOp1 op e ->
      one $
      op1 op =<< evalExpr env e


    EOp2 e1 op e2 ->
      one $
      do x <- evalExpr env e1
         y <- evalExpr env e2
         op2 op x y

    EOpN op es ->
      one $
      opN op =<< evalExprs env es


one :: EvalM a -> EvalM [a]
one x = return <$> x

resolveInstance :: Env -> NodeInst -> EvalM ([ReactValue] -> EvalM [ReactValue])
resolveInstance = undefined
