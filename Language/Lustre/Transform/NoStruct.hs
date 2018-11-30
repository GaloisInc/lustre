{-# Language OverloadedStrings #-}
{- | The purpose of this module is to eliminate structured data.
It should be called after constants have been eliminated, as we then
know that shape of all data. We also assume that function calls have
been names, see "Language.Lustre.Transform.NoStatic". -}
module Language.Lustre.Transform.NoStruct
  (quickNoStruct, StructInfo, StructData(..)
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Maybe(fromMaybe, catMaybes)
import Data.List(genericDrop,genericReplicate,mapAccumL)
import Data.Semigroup ( (<>) )
import Text.PrettyPrint((<+>), braces, brackets, parens)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Transform.NoStatic(CallSiteMap,CallSiteId)
import Language.Lustre.Utils
import Language.Lustre.Panic

type SimpleCallSiteMap = Map Ident (Map CallSiteId [Ident])

-- XXX: More flexible interface
quickNoStruct :: (CallSiteMap,[TopDecl]) ->
                 (Map Ident StructInfo, SimpleCallSiteMap, [TopDecl])
quickNoStruct (csIn,ds) = ( envCollectedInfo env
                          , envSimpleCallSiteMap env
                          , catMaybes mbDs
                          )
  where
  (env,mbDs) = mapAccumL evalTopDecl emptyEnv { envCallSiteMap = csIn } ds


data Env = Env
  { envStructured :: StructInfo
    -- ^ Structure infor for the current node. See "StructInfo"

  , envCollectedInfo :: Map Ident StructInfo
    -- ^ Struct info for already processed nodes.

  , envCallSiteMap :: CallSiteMap
    -- ^ These call sites need to be simlified;
    -- the result is in "envSimpleCallSiteMap"

  , envSimpleCallSiteMap :: SimpleCallSiteMap
    -- ^ Call site info for already processed nodes.


  , envStructs :: Map Name [(Ident,Type)]
    -- ^ Definitions for strcut types.

  , envCurModule :: Maybe Text
    -- ^ If this is 'Just', then we use this to qualify top-level
    -- 'Ident' when we need a name 'Name'
  }


data StructData a = SLeaf a
                  | SArray [StructData a]
                  | STuple [StructData a]
                  | SStruct Name [Field (StructData a)]

instance Functor StructData where
  fmap f st =
    case st of
      SLeaf a      -> SLeaf (f a)
      SArray vs    -> SArray (fmap (fmap f) vs)
      STuple vs    -> STuple (fmap (fmap f) vs)
      SStruct s fs -> SStruct s (fmap (fmap (fmap f)) fs)

instance Foldable StructData where
  foldMap f st =
    case st of
      SLeaf a      -> f a
      SArray vs    -> foldMap (foldMap f) vs
      STuple vs    -> foldMap (foldMap f) vs
      SStruct _ fs -> foldMap (foldMap (foldMap f)) fs

instance Traversable StructData where
  traverse f st =
    case st of
      SLeaf a       -> SLeaf     <$> f a
      SArray vs     -> SArray    <$> traverse (traverse f) vs
      STuple vs     -> STuple    <$> traverse (traverse f) vs
      SStruct x fs  -> SStruct x <$> traverse (traverse (traverse f)) fs



instance Pretty a => Pretty (StructData a) where
  ppPrec n sd =
    case sd of
      SLeaf a      -> ppPrec n a
      SArray as    -> brackets (commaSep (map pp as))
      STuple as    -> parens   (commaSep (map pp as))
      SStruct s fs -> pp s <+> braces (commaSep (map pp fs))

-- | Convert a potentially structured expression (already evaluated)
-- into a list of expressions.
flatStructData :: StructData a -> [a]
flatStructData sd =
  case sd of
    SArray es  -> concatMap flatStructData es
    STuple es  -> concatMap flatStructData es

    -- Here we are assuming that fields are already ordered in some normal form.
    -- Currently, this invariant should be enforced by `NoStatic`, which
    -- places explicit struct fields in the order specified by the struct
    -- declaration.
    SStruct _ fs -> [ v | Field _ e <- fs, v <- flatStructData e ]

    SLeaf a -> [ a ]




{- | Contains the expansions for variables of strucutred types.
For example, if @x : T ^ 3@, then we shoud have a binding
@x = [ x1, x2, x2 ]@.
The expressions in the map should be in evaluated form, which
means that the strucutres data is at the "top" and then we have
variables at the leaves.
-}
type StructInfo = Map Ident (StructData Ident)


-- | An empty environment.
emptyEnv :: Env
emptyEnv = Env
  { envStructured = Map.empty
  , envCollectedInfo = Map.empty
  , envCallSiteMap = Map.empty
  , envSimpleCallSiteMap = Map.empty
  , envStructs    = Map.empty
  , envCurModule  = Nothing
  }

-- | Lookup a name in the structure expansion environment.
-- Since constants are already eliminated, the only things that might
-- be exandable are local variables, which are never qualified.
lkpStrName :: Name -> Env -> Maybe (StructData Ident)
lkpStrName n env =
  case n of
    Unqual i -> Map.lookup i (envStructured env)
    Qual {}  -> Nothing


--------------------------------------------------------------------------------
-- Evaluation of Top Level Declarations

evalTopDecl :: Env -> TopDecl -> (Env, Maybe TopDecl)
evalTopDecl env td =
  case td of
    DeclareType tde     -> addStructDef env tde
    DeclareConst cd     -> panic "evalTopDecl"
                              [ "Unexpecetd constant declaration."
                              , "*** Declaration: " ++ showPP cd ]
    DeclareNode nd      -> (newEnv, Just (DeclareNode node))
      where (info,simp,node) = evalNode env nd
            nm          = nodeName nd
            newEnv = env { envCollectedInfo =
                                      Map.insert nm info (envCollectedInfo env)
                         , envCallSiteMap = Map.delete nm (envCallSiteMap env)
                         , envSimpleCallSiteMap =
                                  Map.insert nm simp (envSimpleCallSiteMap env)
                         }
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
evalNode :: Env -> NodeDecl -> (StructInfo, Map CallSiteId [Ident], NodeDecl)
evalNode env nd
  | null (nodeStaticInputs nd) =
    let prof = nodeProfile nd
        (inMap, inBs)   = expandBinders env (map inB (nodeInputs prof))
        (outMap, outBs) = expandBinders env (nodeOutputs prof)
        -- NOTE: it appears that inputs are not in scope in the outputs in Lus.
        newProf = NodeProfile { nodeInputs = map InputBinder inBs
                              , nodeOutputs = outBs
                              }
        info1 = Map.unions [ inMap, outMap, envStructured env ]
        newEnv = env { envStructured = info1 }
        (newInfo,simp,newDef) =
          case nodeDef nd of
            Nothing -> (info1, Map.empty, Nothing)
            Just body ->
              let todoCS = Map.findWithDefault Map.empty (nodeName nd)
                                                         (envCallSiteMap env)
                  (info, si, body1) = evalNodeBody newEnv todoCS body
              in (info, si, Just body1)

      in ( newInfo
         , simp
         , nd { nodeProfile = newProf
              , nodeDef     = newDef
              }
         )

  | otherwise = panic "evalNode"
                  [ "Unexpected parameterized node."
                  , "Node parameters should have been eliminated by NoStatic."
                  , "*** Node: " ++ showPP nd
                  ]

inB :: InputBinder -> Binder
inB ib =
  case ib of
    InputBinder b -> b
    InputConst i t -> panic "inB"
                        [ "Unexpected input constant:"
                        , "*** Name: " ++ showPP i
                        , "*** Type: " ++ showPP t ]

-- | Evaluate a node's definition.  Expands the local variables,
-- and rewrites the equations.
evalNodeBody :: Env -> Map a [LHS Expression] -> NodeBody ->
                  (StructInfo, Map a [Ident], NodeBody)
evalNodeBody env csTodo body =
  ( newStructInfo
  , simpCS
  , NodeBody { nodeLocals = map LocalVar locBs
             , nodeEqns = concatMap (evalEqn newEnv) (nodeEqns body)
             }
  )
  where
  (locMap, locBs) = expandBinders env [ b | LocalVar b <- nodeLocals body ]
  simpCS          = fmap (concatMap (expandLHS' newEnv)) csTodo
  newEnv          = env { envStructured = newStructInfo }
  newStructInfo   = Map.union locMap (envStructured env)




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
-- For example: if @S = { x : int; y : int^3 }@
-- And we are given the leaves: @[e1,e2,e3,e4]@
-- then, the result will be: @{ x = e1, y = [e2,e3,e4] }@
toNormE :: Env -> Type -> [a] -> StructData a
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
      in (es', SStruct s [ Field l e | ((l,_) ,e) <- zip fs outEs ])

     ArrayType t e ->
       let (es', outEs) = goMany es (genericReplicate (exprToInteger e) t)
       in (es', SArray outEs)

     _ -> case es of
            e : more -> (more, SLeaf e)
            [] -> panic "toNormE" ["Not enogh expressions"]



--------------------------------------------------------------------------------


-- | Expand multiple binders.  For details, have a look at 'expandBinder'.
-- The binders are all evaluated in the same environemnt (i.e., they should
-- not affect each other).
expandBinders ::
  Env -> [Binder] -> (Map Ident (StructData Ident), [Binder])
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
expandBinder :: Env -> Binder -> (Maybe (Ident,StructData Ident), [Binder])
expandBinder env b =
  case expandType env (binderType b) of
    (False,_)  -> (Nothing, [b])
    (True, ts) -> (Just (binderDefines b, expr), bs)
      where
      toBinder x t = Binder { binderDefines = x
                            , binderType    = t
                            , binderClock   = binderClock b
                            }

      bs = zipWith toBinder (nameVariants (binderDefines b)) ts

      expr = toNormE env (binderType b) (map binderDefines bs)

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
    Assert x e   -> case evalExpr env e of
                      SLeaf b -> [ Assert x b ]
                      _ -> panic "evalEqn" ["Assert expects a bool"]
    Property x e -> case evalExpr env e of
                      SLeaf b -> [ Property x b ]
                      _       -> panic "evalEqn" ["PROPERTY expects a bool"]
    IsMain r     -> [ IsMain r ]
    IVC is       -> [ IVC is ]
    Define lhs e
      | [e1] <- es, isCall e1 -> [ Define ls e1 ]
      | otherwise -> zipExact def ls es
      where
      def l a = Define [l] a
      es = flatStructData (evalExpr env e)
      ls = concatMap (expandLHS env) lhs
      isCall ex = case ex of
                    ERange _ ex1 -> isCall ex1
                    Call {}      -> True
                    _            -> False

expandLHS :: Env -> LHS Expression -> [ LHS a ]
expandLHS env lhs = [ LVar i | i <- expandLHS' env lhs ]

-- | Convert a possible complex LHS, to a simple (i.e., identifier) LHS
-- on primitive types.
expandLHS' :: Env -> LHS Expression -> [ Ident ]
expandLHS' env lhs =
  map exprIdLhs (flatStructData (evalExpr env (lhsToExpr lhs)))
  where
  exprIdLhs e =
    case e of
      ERange _ e1    -> exprIdLhs e1
      Var (Unqual i) -> i
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

evalWhen :: StructData Expression -> ClockExpr -> StructData Expression
evalWhen ev ce =
  case ev of
    STuple xs    -> STuple [ x `evalWhen` ce | x <- xs ]
    SArray xs    -> SArray [ x `evalWhen` ce | x <- xs ]
    SStruct s fs -> SStruct s [ Field l (f `evalWhen` ce) | Field l f <- fs ]
    SLeaf e1'    -> SLeaf (e1' `When` ce)


{- | Move a @merege@ to the leaves of structured data.

@ merge c (A -> [1,2]; B -> [3,4])  -->
becomes
[ merge c (A -> 1; B -> 3), merge c (A -> 2; B -> 4) ]
@

Again here we assume that patterns are simple things, as they should be
-}

evalMerge :: Ident -> [MergeCase (StructData Expression)] ->
              StructData Expression
evalMerge i as =
  case as of
    [] -> panic "evalMerge" [ "Empty merge case" ]
    opts@(MergeCase _ o : _) ->
      case getShape o of
        Left _ -> SLeaf (Merge i (map fromLeaf opts))
          where
          fromLeaf a = case a of
                        MergeCase p sh ->
                          case sh of
                            SLeaf e -> MergeCase p e
                            _ -> panic "Type error in merge branch"
                                          [ "Branch: " ++ showPP p
                                          , "Expected: non-structured"
                                          , "Got: structured" ]


        Right sh -> rebuildShape sh mk [ e | MergeCase _ e <- opts ]
          where
          mk es' = evalMerge i
                     [ MergeCase p e | (MergeCase p _, e) <- zip opts es' ]


-- | Lift a binary operator to the leaves of structured data.
-- Assumes that the arguments have the same types, and hence the same shapes.
evalBin :: (Expression -> Expression -> Expression) ->
           StructData Expression ->
           StructData Expression ->
           StructData Expression
evalBin f e1 e2 =
  case (getShape e1,getShape e2) of
    (Left a, Left b) -> SLeaf (f a b)
    (Right sh1, Right sh2)
      | sh1 == sh2 -> rebuildShape sh1 (\ ~[x,y] -> evalBin f x y) [e1,e2]
      | otherwise -> panic "Type error in binary operator"
                       [ "Shape 1:" ++ showPP sh1
                       , "Shape 2:" ++ showPP sh2
                       ]
    _ -> panic "Type error in binary operator (structured vs. not)" []




-- | Evaluate a struct update
evalStructUpdate ::
  Env -> Name {- type -} -> Name -> [Field Expression] -> StructData Expression
evalStructUpdate env s x es =
  case lkpStrName x env of
    Just ev ->
      case ev of
        SStruct s' fs | s == s' ->
          SStruct s
            [ Field l (Map.findWithDefault (toExpr v) l fldMap)
                                                      | Field l v <- fs ]
          where toExpr = fmap (Var . Unqual)


        _ -> panic "evalExpr" [ "Unexpected value to update:"
                              , "*** Expected: a struct"
                              , "*** Expression: " ++ showPP ev
                              ]
    Nothing -> panic "evalExpr"
                    [ "Missing structure expression for:"
                    , "*** Name: " ++ showPP x
                    ]

  where
  fldMap = Map.fromList [ (l, evalExpr env v) | Field l v <- es ]

-- | Select an item from an array.
selectFromArray ::
  Pretty a => [StructData a] -> Selector Integer -> StructData a
selectFromArray vs s =
  case s of

    SelectField f ->
      panic "evalExpr"
        [ "Attempt to select a field from an array."
        , "*** Field: " ++ showPP f
        , "*** Array: " ++ showPP (SArray vs)
        ]

    SelectElement i -> getIx i

    SelectSlice sl ->
      let step  = fromMaybe 1 (arrayStep sl)
          start = arrayStart sl
          ixes  = [ start, start + step .. arrayEnd sl ]
      in SArray (map getIx ixes)

  where
  getIx i = case genericDrop i vs of
              v : _ -> v
              _ -> panic "selectFromArray"
                     [ "Selector out of bounds:"
                     , "*** Index: " ++ show i
                     , "*** Array length: " ++ show (length vs)
                     ]

-- | Select an item from a struct.
selectFromStruct :: Pretty a => Name -> [Field a] -> Selector Integer -> a
selectFromStruct ty fs s =
    case s of

      SelectField i ->
        case [ v | Field l v <- fs, l == i ] of
          v : _ -> v
          _ -> panic "selectFromStruct"
                 [ "Undefined field in selection:"
                 , "*** Field: " ++ showPP i
                 , "*** Struct: " ++ showPP ty
                 , "*** Fields: " ++ show (commaSep (map pp fs))
                 ]

      _ -> panic "selectFromStruct"
             [ "Type error in selector."
             , "*** Selector: " ++ showPP s
             , "*** Struct: " ++ showPP ty
                 , "*** Fields: " ++ show (commaSep (map pp fs))
             ]





-- | Normalize an expression, lifting out structured data to the top.
evalExpr :: Env -> Expression -> StructData Expression
evalExpr env expr =
  case expr of

    ERange _ e -> evalExpr env e

    Var x -> case lkpStrName x env of
               Nothing -> SLeaf expr
               Just e  -> fmap (Var . Unqual) e

    Lit _ -> SLeaf expr

    -- The clock expression are syntactically restricted to not
    -- contain structured data so we don't need to evaluate them.
    e1 `When` ce -> evalWhen (evalExpr env e1) ce

    Tuple es -> STuple (map (evalExpr env) es)

    Array es -> SArray (map (evalExpr env) es)

    Struct s es -> SStruct s [ Field l (evalExpr env e) | Field l e <- es ]
    UpdateStruct s x es -> evalStructUpdate env s x es

    Select e sel ->
        case evalExpr env e of
          SArray vs      -> selectFromArray vs s
          SStruct ty fs  -> selectFromStruct ty fs s
          ev             -> panic "selectFromStruct"
                              [ "Unexpected selection:"
                              , "*** StructData: " ++ showPP ev
                              ]
      where s = evalSelect sel


    WithThenElse {} -> panic "evalExpr"
                        [ "Unexpected with-then-else"
                        , "*** Should have been eliminated by 'NoStatic'"
                        ]

    Merge i as ->
      evalMerge i [ MergeCase p (evalExpr env e) | MergeCase p e <- as ]

    -- XXX: ITERATORS
    Call f es ->
      case (f, map (evalExpr env) es) of

        -- [x1,x2] | [y1,y2]  ~~> [ x1,x2,y1,y2 ]
        (NodeInst (CallPrim _ (Op2 Concat)) [], [e1,e2]) ->
          SArray (asArray e1 ++ asArray e2)
          where asArray x = case x of
                              SArray xs   -> xs
                              _ -> panic "asArray"
                                    [ "Not an array:"
                                    , "*** Expression: " ++ showPP x ]

        -- XXX: This duplicates stuff, perhaps bad
        -- x ^ 2  ~~>  [x,x]
        (NodeInst (CallPrim _ (Op2 Replicate)) [], [e1,_]) ->
          SArray (genericReplicate (exprToInteger (es !! 1)) e1)
          -- NOTE: The second argument is a constant.

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
          SLeaf $ liftFoldBin (bin r Eq) (bin r And) fTrue e1 e2

        -- [x1, x2] <> [y1,y2]  ~~~>  (x1 <> x2) || (y1 <> y2)
        (NodeInst (CallPrim r (Op2 Neq)) [], [e1,e2]) ->
          SLeaf $ liftFoldBin (bin r Neq) (bin r Or) fFalse e1 e2

        -- f([x1,x2])  ~~~>  f(x1,x2)
        (_, evs) -> SLeaf (mkCall f evs)

  where
  mkCall f as = Call f [ v | e <- as, v <- flatStructData e ]

  ite r e1 e2 e3 =
    case e1 of
      SLeaf b -> Call (NodeInst (CallPrim r ITE) []) [b,e2,e3]
      _ -> panic "evalExpr" [ "ITE expects a boolean" ]
  bin r op e1 e2 = Call (NodeInst (CallPrim r (Op2 op)) []) [e1,e2]

  fTrue = Lit (Bool True)
  fFalse = Lit (Bool False)

  liftFoldBin f cons nil e1 e2 =
    fold cons nil (zipWith f (flatStructData e1) (flatStructData e2))

  fold cons nil xs =
    case xs of
      [] -> nil
      _  -> foldr1 cons xs


--------------------------------------------------------------------------------

data Shape = ArrayShape Int | StructShape Name [Ident] | TupleShape Int
              deriving Eq

instance Pretty Shape where
  ppPrec _ sh =
    case sh of
      ArrayShape n -> "array" <+> pp n
      StructShape n fs -> pp n <+> braces (commaSep (map pp fs))
      TupleShape n -> "tuple" <+> pp n


rebuildShape :: Shape ->
                ([StructData Expression] -> StructData Expression) ->
                [ StructData Expression ] -> StructData Expression
rebuildShape sh mk es =
  case sh of

    ArrayShape n -> SArray [ mk (map (getN i) es) | i <- take n [ 0 .. ] ]
      where getN i v = case v of
                         SArray vs ->
                           case drop i vs of
                             el : _ -> el
                             [] -> panic "rebuildShape"
                                    [ "Index out of bounds"
                                    , "*** Index: " ++ show i ]
                         _ -> panic "rebuildShape"
                                [ "Shape mismatch"
                                , "*** Expected: an array"
                                , "*** Got: " ++ showPP v ]


    TupleShape n -> STuple [ mk (map (getN i) es) | i <- take n [ 0 .. ] ]
      where getN i v = case v of
                         STuple vs ->
                           case drop i vs of
                             el : _ -> el
                             [] -> panic "rebuildShape"
                                    [ "Index out of bounds"
                                    , "*** Index: " ++ show i ]
                         _ -> panic "rebuildShape"
                                [ "Shape mismatch"
                                , "*** Expected: a tuple"
                                , "*** Got: " ++ showPP v ]

    StructShape s is -> SStruct s [ Field i (mk (map (getN i) es))
                                                            | i <- is ]
      where getN i v = case v of
                         SStruct s' vs | s == s' ->
                           case [ fv | Field l fv <- vs, l == i ] of
                             el : _ -> el
                             [] -> panic "rebuildShape"
                                    [ "Unknown field"
                                    , "*** Field: " ++ show i ]
                         _ -> panic "rebuildShape"
                                [ "Shape mismatch"
                                , "*** Expected: a struct"
                                , "*** Got: " ++ showPP v ]






-- | Get the outermost shape of an expressio
getShape :: StructData a -> Either a Shape
getShape expr =
  case expr of
    SArray vs     -> Right (ArrayShape (length vs))
    SStruct s fs  -> Right (StructShape s [ l | Field l _ <- fs ])
    STuple vs     -> Right (TupleShape (length vs))
    SLeaf a       -> Left a


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
