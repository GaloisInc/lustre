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
    -- The expressions in the map should be in evaluated form.

  , envStructs :: Map Name [(Ident,Type)]
    -- ^ Definitions for strcut types.

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

--------------------------------------------------------------------------------

-- | Compute the list of atomic types in a type.
expandType :: Env -> Type -> [Type]
expandType env ty =
  case ty of
    TypeRange r t -> map (TypeRange r) (expandType env t)
    NamedType s | Just fs <- Map.lookup s (envStructs env) ->
                      concatMap (expandType env . snd) fs
    ArrayType t e ->
      concat (genericReplicate (exprToInteger e) (expandType env t))

    _ -> [ty]

-- | Given a type, and epxressions for the leaves of a structured value,
-- rebuild the actual value.
toNormE :: Env -> Type -> [Expression] -> Expression
toNormE env t0 es0 =
  case go es0 t0 of
    ([], e) -> e
    _       -> panic "toNormE" [ "Left over expressions after rebuilt" ]
  where
  goMany inEs tys =
    case tys of
      [] -> (inEs , [])
      t : more -> let (rest, outE)   = go inEs t
                      (rest', outEs) = goMany rest more
                  in (rest', outE : outEs)

  go es ty =
   case ty of
     TypeRange _ t -> go es t
     NamedType s | Just fs <- Map.lookup s (envStructs env) ->

      let (es', outEs) = goMany es (map snd fs)
      in (es', Struct s Nothing [ Field l e | ((l,_) ,e) <- zip fs outEs ])

     ArrayType t e ->
       let (es', outEs) = goMany es (genericReplicate (exprToInteger e) t)
       in (es', Array outEs)

     _ -> case es of
            e : more -> (more, e)
            [] -> panic "toNormE" ["Not enogh expressions"]


-- parameters: x : int ^ 3     
-- becomes:
-- 3 parameters: x1, x2, x3 : int
-- x = [ x1, x2, x3 ]
--
-- local x : int ^ 3
-- becomes:
-- 3 locals: x1, x2, x3 : int
-- x = [ x1, x2, x3 ]   -- for references to local
-- in LHS:
-- x --> x1,x2,x3
-- x[1] --> [x1,x2,x3][1] --> x2
--
-- nested case:
-- x : int ^ 2 ^ 3
-- x1 .. x6 : int
-- x = [ [x1,x2], [x3,x4], [x5,x6] ]
-- in LHS:
-- x[0] = ...
-- ->
-- x[0] = [x1,x2] --> x1,x2

type M = IO -- XXX

--------------------------------------------------------------------------------


{- | Move @when@ to the leaves of a structured expressions.
The parameters should be already evaluated.

@[a,b] when c   -->    [a when c, b when c ]@

Note that clock expressions (e.g., `c` above) are small,
so it is OK to duplicate them. -}

evalWhen :: Expression -> ClockExpr -> Expression
evalWhen e ce =
  caseThruRange e $ \ev ->
    case ev of
      Tuple xs -> Tuple [ x `evalWhen` ce | x <- xs ]
      Array xs -> Array [ x `evalWhen` ce | x <- xs ]

      Struct s mb fs ->
        case mb of
          Nothing -> Struct s Nothing
                       [ Field l (f `evalWhen` ce) | Field l f <- fs ]

          Just _  -> panic "evalWhen" [ "Unexpected struct update"
                                      , "*** Expression: " ++ showPP e
                                      ]
      e1' -> e1' `When` ce


{- | Move a @merege@ to the leaves of structured data.
The branches of the case should have been evaluated already.

@ merge c (A -> [1,2]; B -> [3,4])  -->
becomes
[ merge c (A -> 1; B -> 3), merge c (A -> 2; B -> 4) ]
@

Again here we assume that patterns are simple things, as they should be
-}

evalMerge :: Ident -> [MergeCase] -> Expression
evalMerge i as =
  case as of
    [] -> panic "evalMerge" [ "Empty merge case" ]
    opts@(MergeCase _ o : _) ->
      case getShape o of
        Nothing -> Merge i opts
        Just sh -> rebuildShape sh mk [ e | MergeCase _ e <- opts ]
          where
          mk es' = evalMerge i
                     [ MergeCase p e | (MergeCase p _, e) <- zip opts es' ]


-- | Lift a binary operator to the leaves of structured data.
-- Assumes that the arguments have the same types, and hence the same shapes.
evalBin :: (Expression -> Expression -> Expression) ->
           Expression -> Expression -> Expression
evalBin f e1 e2 =
  case getShape e1 of
    Just sh -> rebuildShape sh (\ ~[x,y] -> evalBin f x y) [e1,e2]
    Nothing -> f e1 e2




-- | Evaluate a struct update
evalStructUpdate :: Env -> Name {- type -} -> Name -> [Field] -> Expression
evalStructUpdate env s x es =
  case lkpStrName x env of
    Just e ->
      caseThruRange e $ \ev ->
        case ev of
          Struct s' Nothing fs | s == s' ->
            Struct s Nothing
              [ Field l (Map.findWithDefault v l fldMap) | Field l v <- fs ]


          _ -> panic "evalExpr" [ "Unexpected value to update:"
                                , "*** Expected: a struct"
                                , "*** Expression: " ++ showPP e
                                ]
    Nothing -> panic "evalExpr"
                    [ "Missing structure expression for:"
                    , "*** Name: " ++ showPP x
                    ]

  where
  fldMap = Map.fromList [ (l, evalExpr env v) | Field l v <- es ]

-- | Select an item from an array.
selectFromArray :: [Expression] -> Selector Integer -> Expression
selectFromArray vs s =
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

  where
  getIx i = case genericDrop i vs of
              v : _ -> v
              _ -> panic "selectFromArray"
                     [ "Selector out of bounds:"
                     , "*** Index: " ++ show i
                     , "*** Array: " ++ showPP (Array vs)
                     ]

-- | Select an item from a struct.
selectFromStruct :: Name -> [Field] -> Selector Integer -> Expression
selectFromStruct ty fs s =
    case s of

      SelectField i ->
        case [ v | Field l v <- fs, l == i ] of
          v : _ -> v
          _ -> panic "selectFromStruct"
                 [ "Undefined field in selection:"
                 , "*** Field: " ++ showPP i
                 , "*** Struct: " ++ showPP (Struct ty Nothing fs)
                 ]

      _ -> panic "selectFromStruct"
             [ "Type error in selector."
             , "*** Selector: " ++ showPP s
             , "*** Struct: " ++ showPP (Struct ty Nothing fs)
             ]





-- | Normalize an expression, lifting out structured data to the top.
evalExpr :: Env -> Expression -> Expression
evalExpr env expr =
  case expr of

    ERange r e -> ERange r (evalExpr env e)

    Var x -> case lkpStrName x env of
               Nothing -> expr
               Just e  -> e

    Lit _ -> expr

    -- The clock expression are syntactically restricted to not
    -- contain structured data so we don't need to evaluate them.
    e1 `When` ce -> evalWhen (evalExpr env e1) ce

    Tuple es -> Tuple (map (evalExpr env) es)

    Array es -> Array (map (evalExpr env) es)

    Struct s mb es ->
      case mb of
        Nothing -> Struct s Nothing
                      [ Field l (evalExpr env e) | Field l e <- es ]

        Just x -> evalStructUpdate env s x es

    Select e sel ->

      caseThruRange (evalExpr env e) $ \ev ->
        case ev of
          Array vs              -> selectFromArray vs s
          Struct ty Nothing fs  -> selectFromStruct ty fs s
          _                     -> panic "selectFromStruct"
                                     [ "Selection from a non structured type:"
                                     , "*** Expression: " ++ showPP ev
                                     ]
      where s = evalSelect sel


    WithThenElse {} -> panic "evalExpr"
                        [ "Unexpected with-then-else"
                        , "*** Should have been eliminated by 'NoStatic'"
                        ]

    Merge i as ->
      evalMerge i [ MergeCase p (evalExpr env e) | MergeCase p e <- as ]

    -- XXX: ITERATORS
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
        (NodeInst (CallPrim r (Op2 Fby)) [], [e1,e2]) ->
          evalBin (bin r Fby) e1 e2

        -- if a then [x1,x2] else [y1,y2]  ~~>
        -- [ if a then x1 else y1, if a then x2 else y2 ]
        -- XXX: Duplicates `a`
        (NodeInst (CallPrim r ITE) [], [e1,e2,e3]) ->
          evalBin (\a b -> ite r e1 a b) e2 e3

        -- [x1, x2] = [y1,y2]  ~~~>  (x1 = x2) && (y1 = y2)
        (NodeInst (CallPrim r (Op2 Eq)) [], [e1,e2]) ->
          liftFoldBin (bin r Eq) (bin r And) fTrue e1 e2

        -- [x1, x2] <> [y1,y2]  ~~~>  (x1 <> x2) || (y1 <> y2)
        (NodeInst (CallPrim r (Op2 Neq)) [], [e1,e2]) ->
          liftFoldBin (bin r Neq) (bin r Or) fFalse e1 e2

        -- f([x1,x2])  ~~~>  f(x1,x2)
        (_, evs) -> CallPos f [ v | e <- evs, v <- toMultiExpr e ]

  where
  ite r e1 e2 e3 = CallPos (NodeInst (CallPrim r ITE) []) [e1,e2,e3]
  bin r op e1 e2 = CallPos (NodeInst (CallPrim r (Op2 op)) []) [e1,e2]

  fTrue = Lit (Bool True)
  fFalse = Lit (Bool False)

  liftFoldBin f cons nil e1 e2 =
    fold cons nil (zipWith f (toMultiExpr e1) (toMultiExpr e2))

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
