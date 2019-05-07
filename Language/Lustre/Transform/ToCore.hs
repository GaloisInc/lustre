{-# Language FlexibleInstances #-}
{-# Language OverloadedStrings #-}
{-# Language TypeSynonymInstances #-}
-- | Translate siplified Lustre into the Core representation.
module Language.Lustre.Transform.ToCore
  ( getEnumInfo, evalNodeDecl
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Semigroup ( (<>) )
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Graph.SCC(stronglyConnComp)
import Data.Graph(SCC(..))
import MonadLib hiding (Label)
import AlexTools(SourceRange(..),SourcePos(..))

import Language.Lustre.Name(Ident(..), OrigName(..), Thing(..), identUID
                           , identOrigName, nameOrigName
                           , Label(..))
import qualified Language.Lustre.AST  as P
import qualified Language.Lustre.Core as C
import Language.Lustre.Monad
import Language.Lustre.Panic
import Language.Lustre.Pretty(showPP)


-- | Compute info about enums from some top-level declarations.
-- The result maps the original names of enum constructors, to numeric
-- expressions that should represent them.
getEnumInfo :: [ P.TopDecl ] {- ^ Renamed decls -} -> Map OrigName C.Literal
getEnumInfo tds = foldr addDefs Map.empty enums
  where
  enums = [ is | P.DeclareType
                 P.TypeDecl { P.typeDef = Just (P.IsEnum is) } <- tds ]

  -- The constructors of an enum are represented by 0, 1, .. etc
  addDefs is m = foldr addDef m (zipWith mkDef is [ 0 .. ])

  mkDef i n = (P.identOrigName i, C.Int n)

  addDef (i,n) = Map.insert i n


-- | Translate a node to core form, given information about enumerations.
-- We also return a mapping from original name to core names for translating
-- models back.
evalNodeDecl ::
  Map OrigName C.Literal {- ^ Enum constructor -> expr to represent it -} ->
  P.NodeDecl               {- ^ Simplified source Lustre -} ->
  LustreM C.Node
evalNodeDecl enumCs nd
  | null (P.nodeStaticInputs nd)
  , Just def <- P.nodeDef nd =
      runProcessNode enumCs $
      do let prof = P.nodeProfile nd
         ins  <- mapM evalInputBinder (P.nodeInputs prof)
         outs <- mapM evalBinder (P.nodeOutputs prof)



         locs <- mapM evalBinder
              $ orderBinders [ b | P.LocalVar b <- P.nodeLocals def ]


         eqnss <- mapM evalEqn (P.nodeEqns def)
         asts <- getAssertNames
         props <- getPropertyNames
         pure C.Node { C.nInputs   = ins
                     , C.nOutputs  = [ i | i C.::: _ <- outs ]
                     , C.nAssuming = asts
                     , C.nShows    = props
                     , C.nEqns     = C.orderedEqns (concat eqnss)
                     }

  | otherwise = panic "evalNodeDecl"
                [ "Unexpected node declaration"
                , "*** Node: " ++ showPP nd
                ]

orderBinders :: [P.Binder] -> [P.Binder]
orderBinders = map fromSCC . stronglyConnComp . map depNode
  where
  fromSCC s = case s of
                AcyclicSCC x -> x
                CyclicSCC xs -> panic "ToCore.orderBinders"
                                  ( "Unexpected recursive binder group"
                                  : map (showPP . P.binderDefines) xs
                                  )
  depNode b = (b, identUID (P.binderDefines b),
                  case P.cClock (P.binderType b) of
                    P.BaseClock -> []
                    P.KnownClock (P.WhenClock _ _ i) -> [identUID i]
                    P.ClockVar i -> panic "ToCore.orderBinders"
                                    [ "Unexpected clock variable", showPP i ])


-- | Rewrite a type, replacing named enumeration types with @int@.
evalType :: P.Type -> C.Type
evalType ty =
  case ty of
    P.NamedType {}   -> C.TInt -- Only enum types should be left by now
    P.IntSubrange {} -> C.TInt -- Represented with a number
    P.IntType        -> C.TInt
    P.RealType       -> C.TReal
    P.BoolType       -> C.TBool
    P.TypeRange _ t  -> evalType t
    P.ArrayType {}   -> panic "evalType"
                         [ "Unexpected array type"
                         , "*** Type: " ++ showPP ty
                         ]

--------------------------------------------------------------------------------
type M = StateT St LustreM


runProcessNode :: Map OrigName C.Literal -> M a -> LustreM a
runProcessNode enumCs m =
  do (a,_finS) <- runStateT st m
     pure a
  where
  st = St { stLocalTypes = Map.empty
          , stSrcLocalTypes = Map.empty
          , stGlobEnumCons = enumCs
          , stEqns = []
          , stAssertNames = []
          , stPropertyNames = []
          , stVarMap = Map.empty
          }

data St = St
  { stLocalTypes :: Map OrigName C.CType
    -- ^ Types of local translated variables.
    -- These may change as we generate new equations.

  , stSrcLocalTypes :: Map OrigName C.CType
    -- ^ Types of local variables from the source.
    -- These shouldn't change.

  , stGlobEnumCons  :: Map OrigName C.Literal
    -- ^ Definitions for enum constants.
    -- Currently we assume that these would be int constants.

  , stEqns :: [C.Eqn]
    -- ^ Generated equations naming subcomponents.
    -- Most recently generated first.
    -- Since we process things in depth-first fashion, this should be
    -- reverse to get proper definition order.

  , stAssertNames :: [(Label,OrigName)]
    -- ^ The names of the equations corresponding to asserts.

  , stPropertyNames :: [(Label,OrigName)]
    -- ^ The names of the equatiosn corresponding to properties.


  , stVarMap :: Map OrigName OrigName
    {- ^ Remembers what names we used for values in the core.
    This is so that when we can parse traces into their original names. -}
  }

-- | Get the collected assert names.
getAssertNames :: M [(Label,OrigName)]
getAssertNames = stAssertNames <$> get

-- | Get the collected property names.
getPropertyNames :: M [(Label,OrigName)]
getPropertyNames = stPropertyNames <$> get

-- | Get the map of enumeration constants.
getEnumCons :: M (Map OrigName C.Literal)
getEnumCons = stGlobEnumCons <$> get

-- | Get the collection of local types.
getLocalTypes :: M (Map OrigName C.CType)
getLocalTypes = stLocalTypes <$> get

-- | Record the type of a local.
addLocal :: OrigName -> C.CType -> M ()
addLocal i t = sets_ $ \s -> s { stLocalTypes = Map.insert i t (stLocalTypes s)}

addBinder :: C.Binder -> M ()
addBinder (i C.::: t) = addLocal i t

-- | Generate a fresh local name with the given stemp
newIdentFrom :: Text -> M OrigName
newIdentFrom stem =
  do x <- inBase newInt
     let i = Ident { identLabel    = Label { labText = stem, labRange = noLoc }
                   , identResolved = Nothing
                   }
         o = OrigName { rnUID     = x
                      , rnModule  = Nothing
                      , rnIdent   = i
                      , rnThing   = AVal
                      }
     pure o

  where
  -- XXX: Currently core epxressions have no locations.
  noLoc = SourceRange { sourceFrom = noPos, sourceTo = noPos }
  noPos = SourcePos { sourceIndex = -1, sourceLine = -1
                    , sourceColumn = -1, sourceFile = "" }



-- | Remember an equation.
addEqn :: C.Eqn -> M ()
addEqn eqn@(i C.::: t C.:= _) =
  do sets_ $ \s -> s { stEqns = eqn : stEqns s }
     addLocal i t

-- | Return the collected equations, and clear them.
clearEqns :: M [ C.Eqn ]
clearEqns = sets $ \s -> (stEqns s, s { stEqns = [] })

-- | Generate a fresh name for this expression, record the equation,
-- and return the name.
nameExpr :: C.Expr -> M C.Atom
nameExpr expr =
  do tys <- getLocalTypes
     let t = C.typeOf tys expr
     i <- newIdentFrom stem
     addEqn (i C.::: t C.:= expr)
     pure (C.Var i)

  where
  stem = case expr of
           C.Atom a -> case a of
                         C.Prim op _ -> Text.pack (show op)
                         _ -> panic "nameExpr" [ "Naming a simple atom?"
                                               , "*** Atom:" ++ showPP a ]
           C.Pre a       -> namedStem "pre" a
           _ C.:-> a     -> namedStem "init" a
           C.When _ a    -> namedStem "when" a
           C.Current a   -> namedStem "current" a
           C.Merge a _ _ -> namedStem "merge" a

  namedStem t a = case a of
                    C.Var i -> t <> "_" <> P.origNameTextName i
                    _       -> "$" <> t

-- | Remember that the given identifier was used for an assert.
addAssertName :: Label -> OrigName -> M ()
addAssertName t i = sets_ $ \s -> s { stAssertNames = (t,i) : stAssertNames s }

-- | Remember that the given identifier was used for a property.
addPropertyName :: Label -> OrigName -> M ()
addPropertyName t i =
  sets_ $ \s -> s { stPropertyNames = (t,i) : stPropertyNames s }


--------------------------------------------------------------------------------

evalInputBinder :: P.InputBinder -> M C.Binder
evalInputBinder inp =
  case inp of
    P.InputBinder b -> evalBinder b
    P.InputConst i t ->
      panic "evalInputBinder"
        [ "Unexpected constant parameter"
        , "*** Name: " ++ showPP i
        , "*** Type: " ++ showPP t ]


-- | Add the type of a binder to the environment.
evalBinder :: P.Binder -> M C.Binder
evalBinder b =
  do c <- case P.cClock (P.binderType b) of
            P.BaseClock     -> pure C.BaseClock
            P.KnownClock c  -> C.WhenTrue <$> evalClockExpr c
            P.ClockVar i -> panic "evalBinder"
                              [ "Unexpected clock variable", showPP i ]
     let t = evalType (P.cType (P.binderType b)) `C.On` c
     let xi = identOrigName (P.binderDefines b)
     addLocal xi t
     let bn = xi C.::: t
     addBinder bn
     pure bn

-- | Translate an equation.
-- Invariant: 'stEqns' should be empty before and after this executes.
evalEqn :: P.Equation -> M [C.Eqn]
evalEqn eqn =
  case eqn of
    P.IsMain _ -> pure []
    P.IVC _    -> pure [] -- XXX: we should do something with these
    P.Realizable _ -> pure [] -- XXX: we should do something with these

    P.Property t e -> evalForm "--%PROPERTY" (addPropertyName t) e
    P.Assert t e -> evalForm "assert" (addAssertName t) e

    P.Define ls e ->
      case ls of
        [ P.LVar x ] ->
            do tys <- getLocalTypes
               let x' = identOrigName x
               let t = case Map.lookup x' tys of
                         Just ty -> ty
                         Nothing ->
                            panic "evalEqn" [ "Defining unknown variable:"
                                            , "*** Name: " ++ showPP x ]
               e1  <- evalExpr (Just x') e
               addEqn (x' C.::: t C.:= e1)
               clearEqns


        _ -> panic "evalExpr"
                [ "Unexpected LHS of equation"
                , "*** Equation: " ++ showPP eqn
                ]

  where
  evalForm :: String -> (OrigName -> M ()) -> P.Expression -> M [ C.Eqn ]
  evalForm x f e =
    do e1 <- evalExprAtom e
       case e1 of
         C.Var i ->
           do f i
              clearEqns
         C.Lit n _ ->
          case n of
            C.Bool True  -> pure []
            _ -> panic ("Constant in " ++ x) [ "*** Constant: " ++ show n ]
         C.Prim {} ->
           do ~(C.Var i) <- nameExpr (C.Atom e1)
              f i
              clearEqns



-- | Evaluate a source expression to an a core atom, naming subexpressions
-- as needed.
evalExprAtom :: P.Expression -> M C.Atom
evalExprAtom expr =
  do e1 <- evalExpr Nothing expr
     case e1 of
       C.Atom a -> pure a
       _        -> nameExpr e1


-- | Evaluate a clock-expression to an atom.
evalClockExpr :: P.ClockExpr -> M C.Atom
evalClockExpr (P.WhenClock _ e1 i) =
  do a1  <- evalConstExpr e1
     env <- getLocalTypes
     let a2 = C.Var (identOrigName i)
         ty = C.typeOf env a2
     pure $ case a1 of
              C.Bool True -> a2
              _           -> C.Prim C.Eq [ C.Lit a1 ty, a2 ]

evalIClock :: P.IClock -> M C.Clock
evalIClock clo =
  case clo of
    P.BaseClock -> pure C.BaseClock
    P.KnownClock c -> C.WhenTrue <$> evalClockExpr c
    P.ClockVar {} -> panic "evalIClockExpr" [ "Unexpectec clock variable." ]

evalCurrentWith :: Maybe OrigName -> C.Atom -> C.Atom -> M C.Expr
evalCurrentWith xt d e =
  do env <- getLocalTypes
     let ty = C.typeOf env e
         c@(C.WhenTrue ca) = C.clockOfCType ty
         Just cc = C.clockParent env c
     case xt of
       Just x -> desugar x ca
       Nothing ->
         do i  <- newIdentFrom "curW"
            let thisTy = C.typeOfCType ty `C.On` cc
            addLocal i thisTy
            e1 <- desugar i ca
            addEqn (i C.::: thisTy C.:= e1)
            pure (C.Atom (C.Var i))
  where
  desugar x c =
    do cur  <- nameExpr (C.Current e)
       pre  <- nameExpr (C.Pre (C.Var x))
       hold <- nameExpr (d C.:->  pre)
       pure (C.Atom (C.Prim C.ITE [c,cur,hold]))

evalConstExpr :: P.Expression -> M C.Literal
evalConstExpr expr =
  case expr of
    P.ERange _ e -> evalConstExpr e
    P.Var i ->
      do cons <- getEnumCons
         case Map.lookup (P.nameOrigName i) cons of
          Just e -> pure e
          Nothing -> bad "undefined constant symbol"
    P.Lit l -> pure l
    _ -> bad "constant expression"

  where
  bad msg = panic "evalConstExpr" [ "Unexpected " ++ msg
                             , "*** Expression: " ++ showPP expr
                             ]

evalCType :: P.CType -> M C.CType
evalCType t =
  do c <- evalIClock (P.cClock t)
     pure (evalType (P.cType t) `C.On` c)

-- | Evaluate a source expression to a core expression.
evalExpr :: Maybe OrigName -> P.Expression -> M C.Expr
evalExpr xt expr =
  case expr of
    P.ERange _ e -> evalExpr xt e

    P.Var i -> pure (C.Atom (C.Var (nameOrigName i)))

    P.Const e t ->
      do l <- evalConstExpr e
         ty <- evalCType t
         pure (C.Atom (C.Lit l ty))

    P.Lit {} -> bad "literal outside `Const`."

    e `P.When` ce ->
      do a1 <- evalExprAtom e
         a2 <- evalClockExpr ce
         pure (C.When a1 a2)


    P.Merge i alts ->
      do let j = C.Var (identOrigName i)
         env <- getLocalTypes
         let ty = C.typeOf env j
         as <- forM alts $ \(P.MergeCase k e) -> do p  <- evalConstExpr k
                                                    pure (p,e)
         case as of
           [ (C.Bool b, e1), (_,e2) ] ->
              do e1' <- evalExprAtom e1
                 e2' <- evalExprAtom e2
                 pure $ if b then C.Merge j e1' e2' else C.Merge j e2' e1'
           _ -> go ty j as


      where
      go ty j as =
        case as of
          []  -> bad "empty merge"
          [(_,e)] -> evalExpr Nothing e
          (p,e) : rest ->
             do let b = C.Prim C.Eq [ C.Lit p ty, j ]
                more <- go ty j rest
                l    <- evalExprAtom e
                r    <- case more of
                          C.Atom x -> pure x
                          _        -> nameExpr more
                pure (C.Merge b l r)

    P.Tuple {}  -> bad "tuple"
    P.Array {}  -> bad "array"
    P.Select {} -> bad "selection"
    P.Struct {} -> bad "struct"
    P.UpdateStruct {} -> bad "update-struct"
    P.WithThenElse {} -> bad "with-then-else"

    P.Call ni es cl ->
      do _clv <- evalIClock cl
         {- NOTE: we don't really store the clock of the call anywhere,
         because for primitives (which is all that should be left)
         it can be computed from the clocks of the arguments. -}

         as <- mapM evalExprAtom es
         let prim x = pure (C.Atom (C.Prim x as))
         case ni of
           P.NodeInst (P.CallPrim _ p) [] ->
             case p of

               P.Op1 op1 ->
                 case as of
                   [v] -> case op1 of
                            P.Not      -> prim C.Not
                            P.Neg      -> prim C.Neg
                            P.Pre      -> pure (C.Pre v)
                            P.Current  -> pure (C.Current v)
                            P.IntCast  -> prim C.IntCast
                            P.FloorCast-> prim C.FloorCast
                            P.RealCast -> prim C.RealCast
                   _ -> bad "unary operator"

               P.Op2 op2 ->
                 case as of
                   [v1,v2] -> case op2 of
                                P.Fby       -> do v3 <- nameExpr (C.Pre v2)
                                                  pure (v1 C.:-> v3)
                                P.FbyArr    -> pure (v1 C.:-> v2)
                                P.CurrentWith -> evalCurrentWith xt v1 v2
                                P.And       -> prim C.And
                                P.Or        -> prim C.Or
                                P.Xor       -> prim C.Xor
                                P.Implies   -> prim C.Implies
                                P.Eq        -> prim C.Eq
                                P.Neq       -> prim C.Neq
                                P.Lt        -> prim C.Lt
                                P.Leq       -> prim C.Leq
                                P.Gt        -> prim C.Gt
                                P.Geq       -> prim C.Geq
                                P.Mul       -> prim C.Mul
                                P.Mod       -> prim C.Mod
                                P.Div       -> prim C.Div
                                P.Add       -> prim C.Add
                                P.Sub       -> prim C.Sub
                                P.Power     -> prim C.Power
                                P.Replicate -> bad "`^`"
                                P.Concat    -> bad "`|`"
                   _ -> bad "binary operator"

               P.OpN op ->
                  case op of
                    P.AtMostOne -> prim C.AtMostOne
                    P.Nor       -> prim C.Nor


               P.ITE -> prim C.ITE

               _ -> bad "primitive call"

           _ -> bad "function call"

  where
  bad msg = panic "ToCore.evalExpr" [ "Unexpected " ++ msg
                                    , "*** Expression: " ++ showPP expr
                                    ]
