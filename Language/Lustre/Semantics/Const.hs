module Language.Lustre.Semantics.Const
  ( evalConst, evalSel, evalSelFun, Env(..))
  where

import Data.Map ( Map )
import qualified Data.Map as Map
import Control.Monad(join)

import Language.Lustre.AST
import Language.Lustre.Semantics.Value
import Language.Lustre.Semantics.BuiltIn

data Env = Env
  { envConsts   :: Map Name Value
  , envConstFun :: Map Name ([Value] -> EvalM Value)
  }


-- | Evaluate a constant expression.
evalConst :: Env -> Expression -> EvalM Value
evalConst env expr =
  case expr of

    ERange _ e -> evalConst env e

    Lit l ->
      case l of
        Int n  -> sInt n
        Real n -> sReal n
        Bool n -> sBool n

    IfThenElse b t e ->
      join (sITE <$> evalConst env b <*> evalConst env t <*> evalConst env e)

    WithThenElse be t e ->
      do bv <- evalConst env be
         case bv of
           VBool b -> if b then evalConst env t else evalConst env e
           _       -> typeError "with-then-else" "A `bool`"

    When {}   -> crash "evalConst" "`when` is not a constant expression."
    Merge {}  -> crash "evalConst" "`merge` is not a constant expression."

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


    Tuple {} -> crash "evalConst" "Unexpected constant tuple."

    Array es -> sArray =<< mapM (evalConst env) es

    Struct {} -> error "[evalMultiConst] XXX: Struct"

    Select e sel ->
      do s <- evalSel env sel
         evalSelFun s =<< evalConst env e

    EOp1 op e ->
      do v <- evalConst env e
         case op of
           Not       -> sNot v
           Neg       -> sNeg v
           IntCast   -> sReal2Int v
           RealCast  -> sInt2Real v

           Pre       -> crash "evalMultiConst" "`pre` is not a constant"
           Current   -> crash "evalMultiConst" "`current` is not a constant"

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


-- | Evaluate a selector.
evalSel :: Env -> Selector Expression -> EvalM (Selector Value)
evalSel env sel =
  case sel of

    SelectField f ->
      pure (SelectField f)

    SelectElement ei ->
      do i <- evalConst env ei
         pure (SelectElement i)

    SelectSlice s   ->
      do start <- evalConst env (arrayStart s)
         end   <- evalConst env (arrayEnd s)
         step  <- mapM (evalConst env) (arrayStep s)
         pure (SelectSlice ArraySlice { arrayStart = start
                                      , arrayEnd   = end
                                      , arrayStep  = step
                                      })


-- | Evaluate a selector to a selecting function.
evalSelFun :: Selector Value -> Value -> EvalM Value
evalSelFun sel v =
  case sel of
    SelectField f   -> sSelectField f v
    SelectElement i -> sSelectIndex i v
    SelectSlice s   -> sSelectSlice s v


