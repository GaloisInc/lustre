{-# Language OverloadedStrings #-}
{- | The purpose of this module is to eliminate structured data.
It should be called after constants have been eliminated, as we then
know that shape of all data. We also assume that function calls have
been names, see "Language.Lustre.Transform.NoStatic". -}
module Language.Lustre.Transform.NoStruct (quickNoStruct) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Maybe(fromMaybe, catMaybes)
import Data.List(genericDrop,genericReplicate,mapAccumL)
import Data.Semigroup ( (<>) )

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Utils
import Language.Lustre.Panic

-- XXX: More flexible interface
quickNoStruct :: [TopDecl] -> [TopDecl]
quickNoStruct = catMaybes . snd . mapAccumL evalTopDecl emptyEnv


data Env = Env
  { envStructured :: Map Ident Expression
    -- ^ Contains the expansions for variables of strucutred types.
    -- For example, if @x : T ^ 3@, then we shoud have a binding
    -- @x = [ a, b, c ]@.
    -- The expressions in the map should be in evaluated form.

  , envStructs :: Map Name [(Ident,Type)]
    -- ^ Definitions for strcut types.

  , envCurModule :: Maybe Text
    -- ^ If this is 'Just', then we use this to qualify top-level
    -- 'Ident' when we need a name 'Name'
  }


-- | An empty environment.
emptyEnv :: Env
emptyEnv = Env
  { envStructured = Map.empty
  , envStructs    = Map.empty
  , envCurModule  = Nothing
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
-- Evaluation of Top Level Declarations

evalTopDecl :: Env -> TopDecl -> (Env, Maybe TopDecl)
evalTopDecl env td =
  case td of
    DeclareType tde     -> addStructDef env tde
    DeclareConst cd     -> panic "evalTopDecl"
                              [ "Unexpecetd constant declaration."
                              , "*** Declaration: " ++ showPP cd ]
    DeclareNode nd      -> (env, Just (DeclareNode (evalNode env nd)))
    DeclareNodeInst nid -> panic "evalTopDecl"
                             [ "Node instance declarations should be expanded."
                             , "*** Node instance: " ++ showPP nid
                             ]

-- | Add a structure definition to the environemnt, or do nothing.
addStructDef :: Env -> TypeDecl -> (Env, Maybe TopDecl)
addStructDef env td =
  case typeDef td of
    Just (IsStruct fs) -> (doAddStructDef env (typeName td) fs, Nothing)
    _ -> (env, Just (DeclareType td))

-- | Add a struct definition to the environment. We add an unqialifeid name,
-- and also a qualified one, if a qualifier was provided in the environemnt.
doAddStructDef :: Env -> Ident -> [FieldType] -> Env
doAddStructDef env i fs = env { envStructs = Map.insert (Unqual i) def
                                           $ addQual
                                           $ envStructs env }
  where
  def     = [ (fieldName f, fieldType f) | f <- fs ]
  addQual = case envCurModule env of
              Nothing -> id
              Just m  -> Map.insert (Qual (identRange i) m (identText i)) def


-- | Evaluate a node, expanding structured data.
evalNode :: Env -> NodeDecl -> NodeDecl
evalNode env nd
  | null (nodeStaticInputs nd) =
    let prof = nodeProfile nd
        (inMap, inBs)   = expandBinders env (nodeInputs prof)
        (outMap, outBs) = expandBinders env (nodeOutputs prof)
        -- NOTE: it appears that inputs are not in scope in the outputs in Lus.
        newProf = NodeProfile { nodeInputs = inBs
                              , nodeOutputs = outBs
                              }
        newEnv = env { envStructured = Map.unions [ inMap
                                                  , outMap
                                                  , envStructured env
                                                  ] }
      in nd { nodeProfile = newProf
            , nodeDef     = evalNodeBody newEnv <$> nodeDef nd
            }

  | otherwise = panic "evalNode"
                  [ "Unexpected parameterized node."
                  , "Node parameters should have been eliminated by NoStatic."
                  , "*** Node: " ++ showPP nd
                  ]


-- | Evaluate a node's definition.  Expands the local variables,
-- and rewrites the equations.
evalNodeBody :: Env -> NodeBody -> NodeBody
evalNodeBody env body =
  NodeBody { nodeLocals = map LocalVar locBs
           , nodeEqns = concatMap (evalEqn newEnv) (nodeEqns body)
           }
  where
  (locMap, locBs) = expandBinders env [ b | LocalVar b <- nodeLocals body ]
  newEnv = env { envStructured = Map.union locMap (envStructured env) }




--------------------------------------------------------------------------------
-- Mappings between structured types/data and flat representations.

-- | Compute the list of atomic types in a type.
-- Also returns a boolean to indicate if this was a structured type.
expandType :: Env -> Type -> (Bool, [Type])
expandType env ty =
  case ty of
    TypeRange r t -> (b, map (TypeRange r) ts)
      where (b,ts) = expandType env t
    NamedType s | Just fs <- Map.lookup s (envStructs env) ->
                      (True, concatMap (snd . expandType env . snd) fs)
    ArrayType t e ->
      ( True
      , concat (genericReplicate (exprToInteger e) (snd (expandType env t)))
      )

    _ -> (False, [ty])

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


-- | Expand multiple binders.  For details, have a look at 'expandBinder'.
-- The binders are all evaluated in the same environemnt (i.e., they should
-- not affect each other).
expandBinders :: Env -> [Binder] -> (Map Ident Expression, [Binder])
expandBinders env bs = (Map.fromList (catMaybes defs), concat newBs)
  where
  (defs,newBs) = unzip (map (expandBinder env) bs)


{- | Expand a binder to a list of binder (non-structured binder are left as is).
For structured binders we also return a mapping from the original name,
to its normal form.  For example:

> x : int ^ 3 when t

results in

> x1 : int when t; x2 : int when t; x3 : int when t

and a mapping:

> x = [ x1, x2, x3 ]
-}
expandBinder :: Env -> Binder -> (Maybe (Ident,Expression), [Binder])
expandBinder env b =
  case expandType env (binderType b) of
    (False,_) -> (Nothing, [b])
    (True, ts) -> (Just (binderDefines b, expr), bs)
      where
      toBinder x t = Binder { binderDefines = x
                            , binderType    = t
                            , binderClock   = binderClock b
                            }

      bs = zipWith toBinder (nameVariants (binderDefines b)) ts

      expr = toNormE env (binderType b)
                [ Var (Unqual (binderDefines i)) | i <- bs ]

{- | Given a base name, generate a bunch of different names.
Assuming that the original name is unique, the variants should
also not clash with anything.
XXX: Strictly speaking, this does not avoid name clashes,
so in the future we should make up some alternative scheme.
(the whole naming story could probably use some work). -}
nameVariants :: Ident -> [Ident]
nameVariants i = [ i { identText = t } | t <- nameVariantsText (identText i) ]

-- | Assuming that the original name is unique, the variants should
-- also not clash with anything.
nameVariantsText :: Text -> [Text]
nameVariantsText t = [ variant n | n <- [ 1 :: Integer .. ] ]
  where
  variant n = t <> "_ns_" <> Text.pack (show n)

--------------------------------------------------------------------------------

-- | Expan an equation.  If structured data was involved, the result might
-- be multiple equations.
-- Note that the only equations that have multiple binders on the LHS
-- are ones that have a call on the RHS.
evalEqn :: Env -> Equation -> [Equation]
evalEqn env eqn =
  case eqn of
    Assert e     -> [ Assert (evalExpr env e) ]
    Property e   -> [ Property (evalExpr env e) ]
    IsMain r     -> [ IsMain r ]
    Define lhs e
      | isCall e1 -> [ Define ls e1 ]
      | otherwise -> zipExact def ls (toMultiExpr e1)
      where
      def l a = Define [l] a
      e1 = evalExpr env e
      ls = concatMap (expandLHS env) lhs
      isCall ex = case ex of
                    ERange _ ex1 -> isCall ex1
                    CallPos {}   -> True
                    _            -> False


-- | Convert a possible complex LHS, to a simple (i.e., identifier) LHS
-- on primitive types.
expandLHS :: Env -> LHS Expression -> [ LHS Expression ]
expandLHS env lhs = map exprIdLhs (toMultiExpr (evalExpr env (lhsToExpr lhs)))
  where
  exprIdLhs e =
    case e of
      ERange _ e1    -> exprIdLhs e1
      Var (Unqual i) -> LVar i
      _ -> panic "expandLHS" [ "LHS is not an identifier"
                             , "*** Expression: " ++ showPP e ]

-- | Convert a LHS to an expression corresponding to thing being defined.
lhsToExpr :: LHS Expression -> Expression
lhsToExpr lhs =
  case lhs of
    LVar x      -> Var (Unqual x)
    LSelect l s -> Select (lhsToExpr l) s

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
