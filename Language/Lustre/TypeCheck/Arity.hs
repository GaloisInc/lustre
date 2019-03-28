{-# Language OverloadedStrings #-}
-- | Compute the arities of things.
-- The arity of a thing is how many values does it stands for
-- (i.e., what sort of a tuple are we working with).
module Language.Lustre.TypeCheck.Arity where

import Text.PrettyPrint as PP

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.TypeCheck.Monad


-- | Compute the arity of an expression.
exprArity :: Expression -> M Int
exprArity expr =
  case expr of
    ERange r e          -> inRange r (exprArity e)
    Var {}              -> pure 1
    Lit {}              -> pure 1
    e `When` _          -> exprArity e
    Tuple es            -> pure (length es)
    Array {}            -> pure 1
    Select {}           -> pure 1
    Struct {}           -> pure 1
    UpdateStruct {}     -> pure 1
    WithThenElse _ e2 _ -> exprArity e2
    Merge _ as ->
      case as of
        []    -> reportError "Malformed `merge`---empty alternatives"
        e : _ -> mergeCaseArity e

    Call ni es _ -> nodeInstArtiy ni es

-- | Compute the arity of the given node instantiation when applied to the given argument.
nodeInstArtiy :: NodeInst -> [Expression] -> M Int
nodeInstArtiy (NodeInst call as) es =
  case call of
    CallUser f   ->
      do prof <- niProfile <$> lookupNodeInfo f
         pure $! length (nodeOutputs prof)
    CallPrim r p -> inRange r $ primArity p as es


-- | Compute the arity of a primitive when applied to the given arguments.
-- We always try to compute the arity of the final result type, even if
-- not all arguments are provided.
primArity :: PrimNode -> [StaticArg] -> [Expression] -> M Int
primArity prim as es =
  case prim of
    Iter op ->
      case op of
        IterFill    -> common "fill"
        IterRed     -> common "red"
        IterFillRed -> common "fillred"
        IterMap     -> common "map"
        IterBoolRed -> pure 1
      where
      common nm =
        case as of
          [ n, _ ] ->
            case n of
              NodeArg _ nd -> nodeInstArtiy nd []
              _ -> malformedIterNode nm
          _ -> malformedIter nm 2

    Op1 op ->
      case op of
        Not         -> pure 1
        Neg         -> pure 1
        Pre         -> case es of
                         [e] -> exprArity e
                         _   -> malformed "pre" 1
        Current     -> case es of
                         [e] -> exprArity e
                         _   -> malformed "current" 1
        IntCast     -> pure 1
        FloorCast   -> pure 1
        RealCast    -> pure 1

    Op2 op ->
      case op of
        FbyArr      -> case es of
                         [e, _] -> exprArity e
                         _      -> malformed "->" 2
        Fby         -> case es of
                         [e, _] -> exprArity e
                         _      -> malformed "fby" 2
        CurrentWith -> case es of
                         [e, _] -> exprArity e
                         _      -> malformed "currentWith" 2
        And         -> pure 1
        Or          -> pure 1
        Xor         -> pure 1
        Implies     -> pure 1
        Eq          -> pure 1
        Neq         -> pure 1
        Lt          -> pure 1
        Leq         -> pure 1
        Gt          -> pure 1
        Geq         -> pure 1
        Mul         -> pure 1
        Mod         -> pure 1
        Div         -> pure 1
        Add         -> pure 1
        Sub         -> pure 1
        Power       -> pure 1
        Replicate   -> pure 1
        Concat      -> pure 1

    OpN op ->
      case op of
        AtMostOne -> pure 1
        Nor       -> pure 1

    ITE -> case es of
             [_, e, _ ] -> exprArity e
             _          -> malformed "if-then-else" 3

  where
  malformedIter op expect =
    reportError $ nestedError
       ("Malformed use of iterator" <+> backticks op PP.<> ":")
          [ "Expected:" <+> int expect <+> "static arguments."
          , "Given:" <+> int (length as) <+> "static arguments."
          ]

  malformedIterNode op =
    reportError $ nestedError
       ("Malformed use of iterator" <+> backticks op PP.<> ":")
          [ "Expected a node as the first static argument."
          ]


  malformed op expect =
    reportError $ nestedError
       ("Malformed" <+> backticks op <+> "expression:")
          [ "Expected:" <+> int expect <+> "arguments."
          , "Given:" <+> int (length es) <+> "arguments."
          ]




mergeCaseArity :: MergeCase Expression -> M Int
mergeCaseArity (MergeCase _ e) = exprArity e

