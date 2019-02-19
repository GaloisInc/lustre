{-# Language OverloadedStrings, GeneralizedNewtypeDeriving, DataKinds #-}
{- | The purpose of this module is to eliminate structured data.
It should be called after constants have been eliminated, as we then
know the shape of all data. We also assume that function calls have
been named, see "Language.Lustre.Transform.NoStatic". -}
module Language.Lustre.Transform.NoStruct
  ( NosIn(..), NosOut(..)
  , SimpleCallSiteMap, StructInfo, StructData(..)
  , noStruct
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Maybe(fromMaybe)
import Data.List(genericDrop,genericReplicate)
import Text.PrettyPrint((<+>), braces, brackets, parens)
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Transform.NoStatic(CallSiteMap,CallSiteId)
import Language.Lustre.Monad
import Language.Lustre.Utils
import Language.Lustre.Panic

-- | Information needed to perform the no-structure pass.
data NosIn = NosIn
  { nosiStructs   :: Map OrigName [(Ident,Type)]
    -- ^ Structs from other modules

  , nosiCallSites :: CallSiteMap
    -- ^ Call sites information from the no-static pass
  }

data NosOut = NosOut
  { nosoExpanded  :: Map OrigName StructInfo
    -- ^ Specifies how various identifiers got expanded

  , nosoCallSites :: SimpleCallSiteMap
    -- ^ Processed call sites.
  }

runNosM :: NosIn -> NosM a -> LustreM (NosOut, a)
runNosM ni (NosM m) =
  do (a,s) <- runStateT rw $ runReaderT ro m
     let out = NosOut { nosoExpanded   = rwCollectedInfo s
                      , nosoCallSites  = rwSimpleCallSiteMap s
                      }
     pure (out, a)
  where
  ro = RO { roStructs = nosiStructs ni
          , roCallSiteTodo = nosiCallSites ni
          }
  rw = RW { rwCollectedInfo     = Map.empty
          , rwStructured        = Map.empty
          , rwSimpleCallSiteMap = Map.empty
          }



type SimpleCallSiteMap = Map OrigName (Map CallSiteId [OrigName])

noStruct :: NosIn -> [TopDecl] -> LustreM (NosOut, [TopDecl])
noStruct ni ds = runNosM ni (go [] ds)
  where
  go done todo = case todo of
                   [] -> pure (reverse done)
                   d : more -> evalTopDecl d $ \mb ->
                                 case mb of
                                    Nothing -> go done more
                                    Just d1 -> go (d1 : done) more


data StructData a = SLeaf a
                  | SArray [StructData a]
                  | STuple [StructData a]
                  | SStruct OrigName [Field (StructData a)]

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





--------------------------------------------------------------------------------
-- Evaluation of Top Level Declarations

evalTopDecl :: TopDecl -> (Maybe TopDecl -> NosM a) -> NosM a
evalTopDecl td k =
  case td of
    DeclareType tde     -> evalTypeDecl tde k

    DeclareConst cd     -> panic "evalTopDecl"
                              [ "Unexpecetd constant declaration."
                              , "*** Declaration: " ++ showPP cd ]

    DeclareNode nd -> do node <- evalNode nd
                         k (Just (DeclareNode node))

    DeclareNodeInst nid -> panic "evalTopDecl"
                             [ "Node instance declarations should be expanded."
                             , "*** Node instance: " ++ showPP nid
                             ]

-- | Add a structure definition to the environemnt, or do nothing.
evalTypeDecl :: TypeDecl -> (Maybe TopDecl -> NosM a) -> NosM a
evalTypeDecl td k =
  case typeDef td of
    Just (IsStruct fs) -> doAddStructDef (typeName td) fs (k Nothing)
    _ -> k (Just (DeclareType td))


-- | Evaluate a node, expanding structured data.
evalNode :: NodeDecl -> NosM NodeDecl
evalNode nd =
  do let prof = nodeProfile nd
     inBs   <- expandBinders (map inB (nodeInputs prof))
     outBs  <- expandBinders (nodeOutputs prof)
     let newProf = NodeProfile { nodeInputs  = map InputBinder inBs
                               , nodeOutputs = outBs
                               }

     (simp,newDef) <-
        case nodeDef nd of
          Nothing -> pure (Map.empty, Nothing)
          Just body ->
            do todoCS        <- getCSTodo (identOrigName (nodeName nd))
               (simp, body1) <- evalNodeBody todoCS body
               pure (simp, Just body1)

     finishNode (identOrigName (nodeName nd)) simp

     pure nd { nodeProfile = newProf, nodeDef = newDef }


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
evalNodeBody ::
  Map a [LHS Expression] ->
  NodeBody ->
  NosM (Map a [OrigName], NodeBody)
evalNodeBody csTodo body =
  do locBs <- expandBinders [ b | LocalVar b <- nodeLocals body ]
     simpCS <- traverse (fmap concat . traverse expandLHS') csTodo
     eqns   <- concat <$> traverse evalEqn (nodeEqns body)
     pure ( simpCS
          , NodeBody { nodeLocals = map LocalVar locBs
                     , nodeEqns = eqns
                     }
          )



--------------------------------------------------------------------------------
-- Mappings between structured types/data and flat representations.

-- | Compute the list of atomic types in a type.
-- Also returns a boolean to indicate if this was a structured type.
expandType :: Map OrigName [(Ident,Type)] -> Type -> (Bool, [([SubName],Type)])
expandType env ty =
  case ty of
    TypeRange r t -> (b, [ (n,TypeRange r u) | (n,u) <- ts ])
      where (b,ts) = expandType env t

    -- Named types are either structs or enums.
    NamedType s | Just fs <- Map.lookup (nameOrigName s) env ->
      ( True, [ (StructEl x : n, t)
                | (x,ts) <- fs
                , (n,t)  <- snd (expandType env ts)
                ]
      )

    ArrayType t e ->
      ( True, [ (ArrEl i : n, u)
                | let done = snd (expandType env t)
                , i      <- [ 0 .. exprToInteger e - 1 ]
                , (n,u) <- done
                ]
      )

    _ -> (False, [([],ty)])

data SubName = ArrEl Integer | StructEl Ident


-- | Given a type and epxressions for the leaves of a structured value,
-- rebuild the actual value.
-- For example: if @S = { x : int; y : int^3 }@
-- And we are given the leaves: @[e1,e2,e3,e4]@
-- then, the result will be: @{ x = e1, y = [e2,e3,e4] }@
toNormE :: Map OrigName [ (Ident, Type) ] -> Type -> [a] -> StructData a
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
     NamedType s | Just fs <- Map.lookup (nameOrigName s) env ->

      let (es', outEs) = goMany es (map snd fs)
      in (es', SStruct (nameOrigName s)
                  [ Field l e | ((l,_) ,e) <- zip fs outEs ])

     ArrayType t e ->
       let (es', outEs) = goMany es (genericReplicate (exprToInteger e) t)
       in (es', SArray outEs)

     _ -> case es of
            e : more -> (more, SLeaf e)
            [] -> panic "toNormE" ["Not enogh expressions"]



--------------------------------------------------------------------------------


-- | Expand multiple binders.  For details, have a look at 'expandBinder'.
expandBinders :: [Binder] -> NosM [Binder]
expandBinders bs = concat <$> traverse expandBinder bs

{- | Expand a binder to a list of binder (non-structured binder are left as is).
For structured binders we also return a mapping from the original name,
to its normal form.  For example:

> x : int ^ 3 when t

results in

> x1 : int when t; x2 : int when t; x3 : int when t

and a mapping:

> x = [ x1, x2, x3 ]
-}
expandBinder :: Binder -> NosM [Binder]
expandBinder b =
  do env <- getStructInfo
     case expandType env (binderType b) of
       (False, _) -> pure [b]
       (True, ts) ->
         do bs <- traverse (newSubName b) ts
            let is   = map (identOrigName . binderDefines) bs
                expr = toNormE env (binderType b) is
            addStructured (identOrigName (binderDefines b)) expr
            pure bs







--------------------------------------------------------------------------------

-- | Expan an equation.  If structured data was involved, the result might
-- be multiple equations.
-- Note that the only equations that have multiple binders on the LHS
-- are ones that have a call on the RHS.
evalEqn :: Equation -> NosM [Equation]
evalEqn eqn =
  case eqn of

    Assert x e ->
      do e' <- evalExpr e
         pure (case e' of
                 SLeaf b -> [ Assert x b ]
                 _ -> panic "evalEqn" ["Assert expects a bool"])

    Property x e ->
      do e' <- evalExpr e
         pure (case e' of
                 SLeaf b -> [ Property x b ]
                 _       -> panic "evalEqn" ["PROPERTY expects a bool"])

    IsMain r -> pure [ IsMain r ]

    IVC is -> pure [ IVC is ]

    Define lhs e ->
      do es <- flatStructData <$> evalExpr e
         ls <- concat <$> traverse expandLHS lhs
         pure (case es of
                 [e1] | isCall e1 -> [ Define ls e1 ]
                 _ | otherwise -> zipExact def ls es)

      where
      def l a = Define [l] a
      isCall ex = case ex of
                    ERange _ ex1 -> isCall ex1
                    Call {}      -> True
                    _            -> False

expandLHS :: LHS Expression -> NosM [ LHS a ]
expandLHS lhs = map (LVar . origNameToIdent) <$> expandLHS' lhs

-- | Convert a possible complex LHS, to a simple (i.e., identifier) LHS
-- on primitive types.
expandLHS' :: LHS Expression -> NosM [ OrigName ]
expandLHS' lhs = map exprIdLhs . flatStructData <$> evalExpr (lhsToExpr lhs)
  where
  exprIdLhs e =
    case e of
      ERange _ e1 -> exprIdLhs e1
      Var n       -> nameOrigName n
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
  OrigName {- type -} -> Name -> [Field Expression] -> NosM (StructData Expression)
evalStructUpdate s x es =
  do mb <- lkpStrName x
     case mb of
       Just ev ->
         case ev of
           SStruct s' oldVal | s == s' ->
              do newVals <- traverse evalField es  -- user provided values
                 let newMap = Map.fromList [ (l,e) | Field l e <- newVals ]
                     toExpr = fmap (Var . origNameToName)
                 pure $ SStruct s
                          [ Field l (Map.findWithDefault (toExpr v) l newMap)
                                                         | Field l v <- oldVal ]

           _ -> bad [ "Unexpected value to update:"
                    , "*** Expected: a struct"
                    , "*** Expression: " ++ showPP ev
                    ]

       Nothing -> bad [ "Missing structure expression for:"
                      , "*** Name: " ++ showPP x
                      ]

  where
  bad = panic "evalStructUpdate"

-- | Select an item from an array.
selectFromArray ::
  Pretty a => [StructData a] -> Selector Integer -> StructData a
selectFromArray vs s =
  case s of

    SelectField f ->
      panic "selectFromArray"
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
selectFromStruct :: Pretty a => OrigName -> [Field a] -> Selector Integer -> a
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
evalExpr :: Expression -> NosM (StructData Expression)
evalExpr expr =
  case expr of

    ERange _ e -> evalExpr e

    Var x ->
      do mb <- lkpStrName x
         pure (case mb of
                 Nothing -> SLeaf expr
                 Just y  -> Var . origNameToName <$> y)

    Lit _ -> pure (SLeaf expr)

    -- The clock expression are syntactically restricted to not
    -- contain structured data so we don't need to evaluate them.
    e1 `When` ce ->
      do e1' <- evalExpr e1
         pure (evalWhen e1' ce)

    Tuple es -> STuple <$> traverse evalExpr es
    Array es -> SArray <$> traverse evalExpr es

    Struct s fs         -> SStruct (nameOrigName s) <$> traverse evalField fs
    UpdateStruct s x es -> evalStructUpdate (nameOrigName s) x es

    Select e sel ->
      do e1 <- evalExpr e
         let s = evalSelect sel
         pure (case e1 of
                 SArray vs      -> selectFromArray vs s
                 SStruct ty fs  -> selectFromStruct ty fs s
                 ev             -> panic "selectFromStruct"
                                     [ "Unexpected selection:"
                                     , "*** StructData: " ++ showPP ev
                                     ])

    WithThenElse {} -> panic "evalExpr"
                        [ "Unexpected with-then-else"
                        , "*** Should have been eliminated by 'NoStatic'"
                        ]

    Merge i as -> evalMerge i <$> traverse evBranch as
      where evBranch (MergeCase p e) = MergeCase p <$> evalExpr e

    -- XXX: ITERATORS
    Call f es ->
      do es' <- traverse evalExpr es
         pure $
           case (f, es') of

             -- [x1,x2] | [y1,y2]  ~~> [ x1,x2,y1,y2 ]
             (NodeInst (CallPrim _ (Op2 Concat)) [], [e1,e2]) ->
               SArray (asArray e1 ++ asArray e2)
               where asArray x = case x of
                                   SArray xs -> xs
                                   _ -> panic "evalExpr.asArray"
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

             -- [x1, x2] fby [y1,y2]   ~~~>   [ x1 ~~> y1, x2 ~~> y2 ]
             (NodeInst (CallPrim r (Op2 FbyArr)) [], [e1,e2]) ->
               evalBin (bin r FbyArr) e1 e2

             -- pre [x,y] ~~~> [pre x, pre y]
             (NodeInst (CallPrim _ (Op1 Pre)) [], args) ->
                 case args of
                   [e] -> pre <$> e
                   _   -> STuple [ pre <$> e | e <- args ]
                  where pre a = Call f [a]

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

evalField :: Field Expression -> NosM (Field (StructData Expression))
evalField (Field l e) = Field l <$> evalExpr e

--------------------------------------------------------------------------------

data Shape = ArrayShape Int | StructShape OrigName [Ident] | TupleShape Int
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


--------------------------------------------------------------------------------

newtype NosM a = NosM { unNosM :: WithBase LustreM
                                     [ ReaderT RO
                                     , StateT  RW
                                     ] a }
  deriving (Functor,Applicative,Monad)

data RO = RO
  { roStructs      :: !(Map OrigName [(Ident,Type)])
    -- ^ Information about struct type defs in scope.

  , roCallSiteTodo :: !CallSiteMap
    -- ^ These call sites need to be simlified;
    -- the result is in "rwSimpleCallSiteMap"
  }

data RW = RW
  { rwCollectedInfo     :: !(Map OrigName StructInfo)
    -- ^ Struct info for already processed nodes.

  , rwStructured        :: !StructInfo
    -- ^ Structure info for the current node. See "StructInfo"

  , rwSimpleCallSiteMap :: !SimpleCallSiteMap
    -- ^ Call site info for already processed nodes.
  }

{- | Contains the expansions for variables of strucutred types.
For example, if @x : T ^ 3@, then we shoud have a binding
@x = [ x1, x2, x2 ]@.
The expressions in the map should be in evaluated form, which
means that the strucutres data is at the "top" and then we have
variables at the leaves.
-}
type StructInfo = Map OrigName (StructData OrigName)



-- | Make a new binder, naming a sub-component of the given binder.
newSubName :: Binder -> ([SubName],Type) -> NosM Binder
newSubName b (p,t) = NosM $
  do n <- inBase newInt
     let oldName = binderDefines b
         newText = newSubText (identText oldName) p
         newName = OrigName
                     { rnUID     = n
                     , rnModule  = Nothing
                     , rnIdent   = oldName { identText     = newText
                                           , identResolved = Nothing }
                     , rnThing   = AVal
                     }

     pure Binder { binderDefines = origNameToIdent newName
                 , binderType    = t
                 , binderClock   = binderClock b
                 }
  where
  newSubText u ps = Text.concat (u : map toText ps)
  toText q = case q of
               ArrEl n    -> Text.pack ("[" ++ show n ++ "]")
               StructEl f -> "." `Text.append` identText f


-- | Lookup the definition of a struct type, or 'Nothing' if the
-- name of the type is not a struct (i.e., it is an enum).
getStructInfo :: NosM (Map OrigName [ (Ident,Type)])
getStructInfo = NosM (roStructs <$> ask)

-- | Get what call sites we need to process.
-- These are passed in from the the NoStatic pass.
getCSTodo :: OrigName -> NosM (Map CallSiteId [LHS Expression])
getCSTodo nm =
  do cs <- NosM (roCallSiteTodo <$> ask)
     pure (Map.findWithDefault Map.empty nm cs)

-- | Add information for an expanded local binder.
addStructured :: OrigName -> StructData OrigName -> NosM ()
addStructured x i = NosM $ sets_ $ \s ->
                          s { rwStructured = Map.insert x i (rwStructured s) }

-- | Lookup information about a strucutred local.
lkpStrName :: Name -> NosM (Maybe (StructData OrigName))
lkpStrName n = Map.lookup (nameOrigName n) . rwStructured <$> NosM get



-- | Record information about the expanded binders in a module,
-- and reset the field, so that we can process the next module correctly.
finishNode :: OrigName -> Map CallSiteId [OrigName] -> NosM ()
finishNode nm simp = NosM $ sets_ $ \s ->
  s { rwCollectedInfo     = Map.insert nm (rwStructured s) (rwCollectedInfo s)
    , rwStructured        = Map.empty
    , rwSimpleCallSiteMap = Map.insert nm simp (rwSimpleCallSiteMap s)
    }

-- | Add a struct definition to the environment.
doAddStructDef :: Ident -> [FieldType] -> NosM a -> NosM a
doAddStructDef i fs m =
  do ro <- NosM ask
     let def = [ (fieldName f, fieldType f) | f <- fs ]
         ro1 = ro { roStructs = Map.insert (identOrigName i) def (roStructs ro)}
     NosM (local ro1 (unNosM m))



