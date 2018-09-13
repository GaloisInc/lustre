{- | The purpose of this module is to eliminate structured data.
It should be called after constants have been eliminated, as we then
know that shape of all data. We also assume that function calls have
been names, see "Language.Lustre.Transform.NoStatic". -}
module Language.Lustre.Transform.NoStruct where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe(fromMaybe)
import Data.List(genericDrop,genericReplicate)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic


data Env = Env
  { envStructured :: Map Ident Expression
    -- ^ Contains the expansions for variables of strucutred types.
    -- For example, if @x : T ^ 3@, then we shoud have a binding
    -- @x = [ a, b, c ]@.

  , nodeTypes :: Map Name NodeProfile
    -- ^ Information about the types of the nodes that are in scope.
  }

-- | Lookup a name in the structure expansion environment.
-- Since constants are already eliminated, the only things that might
-- be exandable are local variables, which are never qualified.
lkpStrName :: Name -> Env -> Maybe Expression
lkpStrName n env =
  case n of
    Unqual i -> Map.lookup i (envStructured env)
    Qual {}  -> Nothing

-- | Apply a function but only after you skip all range annotations.
-- They are applied to the result of the function.
caseThruRange :: Expression -> (Expression -> Expression) -> Expression
caseThruRange expr f =
  case expr of
    ERange r e -> ERange r (caseThruRange e f)
    _          -> f expr

-- | Normalize an expression, lifting out structured data to the top.
evalExpr :: Env -> Expression -> Expression
evalExpr env expr =
  case expr of

    ERange r e -> ERange r (evalExpr env e)

    Var x -> case lkpStrName x env of
               Nothing -> expr
               Just e  -> e

    Lit _ -> expr

    {- [a,b] when c   -->    [a when c, b when c ]

    Note that clock expressions (e.g., `c` above) are small,
    so it is OK to duplicate them.  We also assume that they don't contain
    structured data, which is why we don't evaluate them---
    they are supposed to be simple expressions (e.g., no selectors)
    of boolean or enum type. -}
    e1 `When` ce ->

      caseThruRange (evalExpr env e1) $ \ev ->
        case ev of
          Tuple xs -> Tuple [ x `When` ce | x <- xs ]
          Array xs -> Array [ x `When` ce | x <- xs ]

          Struct s mb fs ->
            case mb of
              Nothing -> Struct s Nothing
                           [ Field l (e `When` ce) | Field l e <- fs ]

              Just _  -> panic "evalExpr" [ "Unexpected update"
                                          , "*** Expression: " ++ showPP expr
                                          ]
          e1' -> e1' `When` ce

    Tuple es -> Tuple (map (evalExpr env) es)

    Array es -> Array (map (evalExpr env) es)

    Struct s mb es ->
      case mb of
        Nothing -> Struct s Nothing
                      [ Field l (evalExpr env e) | Field l e <- es ]
        Just x ->
          case lkpStrName x env of
            Just e ->
              caseThruRange e $ \ev ->
                case ev of
                  Struct s' Nothing fs | s == s' ->
                    Struct s Nothing
                      [ Field l (Map.findWithDefault v l exprMap)
                                                      | Field l v <- fs ]
                    where
                    exprMap = Map.fromList
                               [ (l, evalExpr env v) | Field l v <- es ]


                  _ -> panic "evalExpr" [ "Unexpected value to update:"
                                        , "*** Expected: a struct"
                                        , "*** Expression: " ++ showPP e
                                        ]

            Nothing -> panic "evalExpr"
                            [ "Missing structure expression for:"
                            , "*** Name: " ++ showPP x
                            ]

    Select e sel ->

      caseThruRange (evalExpr env e) $ \ev ->
        case ev of

          Array vs ->
            case s of

              SelectField f ->
                panic "evalExpr"
                  [ "Attempt to select a field from an array."
                  , "*** Field: " ++ showPP f
                  , "*** ArrayL " ++ showPP (Array vs)
                  ]

              SelectElement i -> getIx i

              SelectSlice sl ->
                let step  = fromMaybe 1 (arrayStep sl)
                    start = arrayStart sl
                    ixes  = [ start, start + step .. arrayEnd sl ]
                in Array (map getIx ixes)

            where getIx i =
                    case genericDrop i vs of
                      v : _ -> v
                      _ -> panic "evalExpr"
                             [ "Selector out of bounds:"
                             , "*** Index: " ++ show i
                             , "*** Array: " ++ showPP (Array vs)
                             ]

          Struct _ Nothing fs ->
            case s of

              SelectField i ->
                case [ v | Field l v <- fs, l == i ] of
                  v : _ -> v
                  _ -> panic "evalExpr"
                         [ "Undefined field in selection:"
                         , "*** Field: " ++ showPP i
                         , "*** Struct: " ++ showPP ev
                         ]

              _ -> panic "evalExpr"
                     [ "Type error in selector."
                     , "*** Selector: " ++ showPP s
                     , "*** Struct: " ++ showPP ev
                     ]

          _ -> panic "evalExpr"
                  [ "Selection from a non structured type:"
                  , "*** Expression: " ++ showPP ev
                  ]

      where s = evalSelect sel


    WithThenElse {} -> panic "evalExpr"
                        [ "Unexpected with-then-else"
                        , "*** Should have been eliminated by 'NoStatic'"
                        ]

    -- merge c (A -> [1,2]; B -> [3,4])  -->
    -- becomes
    -- [ merge c (A -> 1; B -> 3), merge c (A -> 2; B -> 4) ]
    --
    -- Again here we assume that patterns are simple things, as they should be
    Merge i as ->
      case [ MergeCase p (evalExpr env e) | MergeCase p e <- as ] of
        [] -> panic "evalExpr" [ "Empty merge case" ]
        opts@(MergeCase _ o : _) ->
          case getShape o of
            Nothing -> Merge i opts
            Just sh -> rebuildShape sh mk [ e | MergeCase _ e <- opts ]
              where mk es' = Merge i [ MergeCase p e |
                                          (MergeCase p _, e) <- zip opts es' ]

    CallPos f es ->
      case (f, map (evalExpr env) es) of

        -- [x1,x2] | [y1,y2]  ~~> [ x1,x2,y1,y2 ]
        (NodeInst (CallPrim _ (Op2 Concat)) [], [e1,e2]) ->
          Array (asArray e1 ++ asArray e2)
          where asArray x = case x of
                              ERange _ y -> asArray y
                              Array xs   -> xs
                              _ -> panic "asArray"
                                    [ "Not an array:"
                                    , "*** Expression: " ++ showPP x ]

        -- XXX: This duplicates stuff, perhaps bad
        -- x ^ 2  ~~>  [x,x]
        (NodeInst (CallPrim _ (Op2 Replicate)) [], [e1,e2]) ->
          Array (genericReplicate (exprToInteger e2) e1)

        -- [x1, x2] fby [y1,y2]   ~~~>   [ x1 ~~> y1, x2 ~~> y2 ]
        (NodeInst (CallPrim r (Op2 Fby)) [], [e1,e2])
          | Just res <- liftBin (bin r Fby) e1 e2 -> res

        -- if a then [x1,x2] else [y1,y2]  ~~>
        -- [ if a then x1 else y1, if a then x2 else y2 ]
        -- XXX: Duplicates `a`
        (NodeInst (CallPrim r ITE) [], [e1,e2,e3])
          | Just res <- liftBin (\a b -> ite r e1 a b) e2 e3 -> res

        -- [x1, x2] = [y1,y2]  ~~~>  (x1 = x2) && (y1 = y2)
        (NodeInst (CallPrim r (Op2 Eq)) [], [e1,e2])
          | Just res <- liftFoldBin (bin r Eq) (bin r And) fTrue e1 e2 -> res

        -- [x1, x2] <> [y1,y2]  ~~~>  (x1 <> x2) || (y1 <> y2)
        (NodeInst (CallPrim r (Op2 Neq)) [], [e1,e2])
          | Just res <- liftFoldBin (bin r Neq) (bin r Or) fFalse e1 e2 -> res

        -- f([x1,x2])  ~~~>  f(x1,x2)
        (_, evs) -> CallPos f [ v | e <- evs, v <- toMultiExpr e ]

  where
  ite r e1 e2 e3 = CallPos (NodeInst (CallPrim r ITE) []) [e1,e2,e3]
  bin r op e1 e2 = CallPos (NodeInst (CallPrim r (Op2 op)) []) [e1,e2]

  fTrue = Lit (Bool True)
  fFalse = Lit (Bool False)

  liftBin f e1 e2 =
    do sh <- getShape e1
       pure (rebuildShape sh (\ ~[x,y] -> f x y) [e1,e2])

  liftFoldBin f cons nil e1 e2 =
    do r <- liftBin f e1 e2
       pure $ case r of
                Array as            -> fold cons nil as
                Struct _ Nothing fs -> fold cons nil [ e | Field _ e <- fs ]
                Tuple es            -> fold cons nil es
                _ -> panic "liftFoldBin"
                       [ "Unexpected result of `rebuildShape`"
                       , "*** Expression: " ++ showPP r ]
  fold cons nil xs =
    case xs of
      [] -> nil
      _  -> foldr1 cons xs


-- | Convert a potentially structured expression (already evaluated)
-- into a list of expressions.
toMultiExpr :: Expression -> [Expression]
toMultiExpr expr =
  case expr of
    ERange r e    -> case toMultiExpr e of
                       [e1] -> [ ERange r e1 ]
                       es   -> es
    Array es      -> concatMap toMultiExpr es
    Tuple es      -> concatMap toMultiExpr es

    -- Here we are assuming that fields are already in some normal form.
    -- Currently, this invariant should be enforced by `NoStatic`, which
    -- places explicit struct fields in the order specified by the struct
    -- declaration.
    Struct _ _ fs -> [ v | Field _ e <- fs, v <- toMultiExpr e ]

    _             -> [ expr ]


--------------------------------------------------------------------------------

data Shape = ArrayShape Int | StructShape Name [Ident] | TupleShape Int

rebuildShape :: Shape ->
                ([Expression] -> Expression) ->
                [ Expression ] ->
                Expression
rebuildShape sh mk es =
  case sh of

    ArrayShape n -> Array [ mk (map (getN i) es) | i <- take n [ 0 .. ] ]
      where getN i e = caseThruRange e $ \v ->
                       case v of
                         Array vs ->
                           case drop i vs of
                             el : _ -> el
                             [] -> panic "rebuildShape"
                                    [ "Index out of bounds"
                                    , "*** Index: " ++ show i ]
                         _ -> panic "rebuildShape"
                                [ "Shape mismatch"
                                , "*** Expected: an array"
                                , "*** Got: " ++ showPP v ]


    TupleShape n -> Tuple [ mk (map (getN i) es) | i <- take n [ 0 .. ] ]
      where getN i e = caseThruRange e $ \v ->
                       case v of
                         Tuple vs ->
                           case drop i vs of
                             el : _ -> el
                             [] -> panic "rebuildShape"
                                    [ "Index out of bounds"
                                    , "*** Index: " ++ show i ]
                         _ -> panic "rebuildShape"
                                [ "Shape mismatch"
                                , "*** Expected: a tuple"
                                , "*** Got: " ++ showPP v ]

    StructShape s is -> Struct s Nothing [ Field i (mk (map (getN i) es))
                                                            | i <- is ]
      where getN i e = caseThruRange e $ \v ->
                       case v of
                         Struct s' Nothing vs | s == s' ->
                           case [ fv | Field l fv <- vs, l == i ] of
                             el : _ -> el
                             [] -> panic "rebuildShape"
                                    [ "Unknown field"
                                    , "*** Field: " ++ show i ]
                         _ -> panic "rebuildShape"
                                [ "Shape mismatch"
                                , "*** Expected: a struct"
                                , "*** Got: " ++ showPP v ]






-- | Get the shape of an expressio.
getShape :: Expression -> Maybe Shape
getShape expr =
  case expr of
    ERange _ e -> getShape e
    Array vs   -> Just (ArrayShape (length vs))
    Struct s Nothing fs -> Just (StructShape s [ l | Field l _ <- fs ])
    Tuple vs -> Just (TupleShape (length vs))
    _ -> Nothing


-- | Convert a literal expression to integer, or panic.
exprToInteger :: Expression -> Integer
exprToInteger expr =
  case expr of
    ERange _ e   -> exprToInteger e
    Lit (Int x) -> x
    _ -> panic "exprToInteger"
           [ "The expression is not an integer constant:"
           , "*** Expression: " ++ showPP expr
           ]

-- | Eval a selector.  Since all comstants are expanded, the selectors
-- would be known integers.
evalSelect :: Selector Expression -> Selector Integer
evalSelect sel =
  case sel of
    SelectField i   -> SelectField i
    SelectElement e -> SelectElement (exprToInteger e)
    SelectSlice s   -> SelectSlice (evalSlice s)

-- | Evaluate a sllice, replacing literal expressions with integers.
evalSlice :: ArraySlice Expression -> ArraySlice Integer
evalSlice s = ArraySlice { arrayStart = exprToInteger (arrayStart s)
                         , arrayEnd   = exprToInteger (arrayEnd s)
                         , arrayStep  = exprToInteger <$> arrayStep s
                         }
