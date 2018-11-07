{-# Language OverloadedStrings #-}
module Language.Lustre.Transform.ToCore
  ( getEnumInfo, evalNodeDecl
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Semigroup ( (<>) )
import Data.Text (Text)
import qualified Data.Text as Text
import MonadLib

import qualified Language.Lustre.AST  as P
import qualified Language.Lustre.Core as C
import Language.Lustre.Panic
import Language.Lustre.Pretty(showPP)


-- | Compute info about enums from some top-level declarations.
getEnumInfo :: Maybe Text -> [ P.TopDecl ] -> Map P.Name C.Expr
getEnumInfo mbCur tds = foldr addDefs Map.empty enums
  where
  enums = [ is | P.DeclareType
                 P.TypeDecl { P.typeDef = Just (P.IsEnum is) } <- tds ]

  addDefs is m = foldr addDef m (zipWith mkDef is [ 0 .. ])

  mkDef i n = (i, C.Atom (C.Lit (C.Int n)))

  addDef (i,n) = Map.insert (P.Unqual i) n . addQual i n

  addQual i x =
    case mbCur of
     Nothing -> id
     Just m -> Map.insert (P.Qual (P.identRange i) m (P.identText i)) x


-- | Translate a node to core form, given information about enumerations.
-- We also return a mapping from original name to core names for translating
-- models back.
evalNodeDecl :: Map P.Name C.Expr -> P.NodeDecl -> (Map P.Ident C.Ident, C.Node)
evalNodeDecl enumCs nd
  | null (P.nodeStaticInputs nd)
  , Just def <- P.nodeDef nd =
      runProcessNode enumCs $
      do let prof = P.nodeProfile nd
         ins  <- mapM evalBinder (P.nodeInputs prof)
         outs <- mapM evalBinder (P.nodeOutputs prof)
         mapM_ addBinder ins
         mapM_ addBinder outs
         locs <- mapM evalBinder [ b | P.LocalVar b <- P.nodeLocals def ]
         mapM_ addBinder locs
         eqnss <- mapM evalEqn (P.nodeEqns def)
         asts <- getAssertNames
         props <- getPropertyNames
         varMp <- getVarMap
         pure (varMp
              , C.Node { C.nInputs   = ins
                     , C.nOutputs  = [ i | i C.::: _ <- outs ]
                     , C.nAssuming = asts
                     , C.nShows    = props
                     , C.nEqns     = concat eqnss
                     })

  | otherwise = panic "evalNodeDecl"
                [ "Unexpected node declaration"
                , "*** Node: " ++ showPP nd
                ]




-- | Rewrite a type, replacing named enumeration types with @int@.
evalType :: P.Type -> C.Type
evalType ty =
  case ty of
    P.NamedType {}   -> C.TInt -- ^ Only enum types should be left by now
    P.IntSubrange {} -> C.TInt -- ^ Represented with a number
    P.IntType        -> C.TInt
    P.RealType       -> C.TReal
    P.BoolType       -> C.TBool
    P.TypeRange _ t  -> evalType t
    P.TVar x         -> panic "evalType" [ "Unexpecte type variable"
                                         , "*** Tvar: " ++ showPP x ]

    P.ArrayType {}   -> panic "evalType"
                         [ "Unexpected array type"
                         , "*** Type: " ++ showPP ty
                         ]

--------------------------------------------------------------------------------
type M = StateT St Id

runProcessNode :: Map P.Name C.Expr -> M a -> a
runProcessNode enumCs m = fst $ runId $ runStateT st m
  where
  st = St { stLocalTypes = Map.empty
          , stSrcLocalTypes = Map.empty
          , stGlobEnumCons = enumCs
          , stNameSeed = 1
          , stEqns = []
          , stAssertNames = []
          , stPropertyNames = []
          , stVarMap = Map.empty
          }

data St = St
  { stLocalTypes :: Map C.Ident C.CType
    -- ^ Types of local translated variables.
    -- These may change as we generate new equations.

  , stSrcLocalTypes :: Map P.Ident C.CType
    -- ^ Types of local variables from the source.
    -- These shouldn't change.

  , stGlobEnumCons  :: Map P.Name C.Expr
    -- ^ Definitions for enum constants.
    -- Currently we assume that these would be int constants.

  , stNameSeed :: !Int
    -- ^ Used to generate names when we name sub-expressions

  , stEqns :: [C.Eqn]
    -- ^ Generated equations naming subcomponents.
    -- Most recently generated first.
    -- Since we process things in depth-first fashion, this should be
    -- reverse to get proper definition order.

  , stAssertNames :: [(Text,C.Ident)]
    -- ^ The names of the equations corresponding to asserts.

  , stPropertyNames :: [(Text,C.Ident)]
    -- ^ The names of the equatiosn corresponding to properties.


  , stVarMap :: Map P.Ident C.Ident
    {- ^ Remembers what names we used for values in the core.
    This is so that when we can parse traces into their original names. -}
  }

-- | Get the collected assert names.
getAssertNames :: M [(Text,C.Ident)]
getAssertNames = stAssertNames <$> get

-- | Get the collected property names.
getPropertyNames :: M [(Text,C.Ident)]
getPropertyNames = stPropertyNames <$> get

-- | Get the map of enumeration constants.
getEnumCons :: M (Map P.Name C.Expr)
getEnumCons = stGlobEnumCons <$> get

-- | Get the collection of local types.
getLocalTypes :: M (Map C.Ident C.CType)
getLocalTypes = stLocalTypes <$> get

-- | Get the types of the untranslated locals.
getSrcLocalTypes :: M (Map P.Ident C.CType)
getSrcLocalTypes = stSrcLocalTypes <$> get

-- | Record the type of a local.
addLocal :: C.Ident -> C.CType -> M ()
addLocal i t = sets_ $ \s -> s { stLocalTypes = Map.insert i t (stLocalTypes s)}

addBinder :: C.Binder -> M ()
addBinder (i C.::: t) = addLocal i t

-- | Add a type for a declared local.
addSrcLocal :: P.Ident -> C.CType -> M ()
addSrcLocal x t = sets_ $ \s ->
  s { stSrcLocalTypes = Map.insert x t (stSrcLocalTypes s)
    , stGlobEnumCons  = Map.delete (P.Unqual x) (stGlobEnumCons s)
    }

-- | Generate a fresh identifier.
newIdent :: M C.Ident
newIdent = sets $ \s ->
  let x = stNameSeed s
      i = C.Ident ("__core_" <> Text.pack (show x))
  in (i, s { stNameSeed = 1 + stNameSeed s })

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
     case C.typeOf tys expr of
       Just t ->
          do i <- newIdent
             addEqn (i C.::: t C.:= expr)
             pure (C.Var i)
       Nothing -> panic "nameExpr" [ "Failed to compute the type of:"
                                   , "*** Expression: " ++ showPP expr
                                   , "*** Types: " ++ show tys
                                   ]

-- | Remember that the given identifier was used for an assert.
addAssertName :: Text -> C.Ident -> M ()
addAssertName t i = sets_ $ \s -> s { stAssertNames = (t,i) : stAssertNames s }

-- | Remember that the given identifier was used for a property.
addPropertyName :: Text -> C.Ident -> M ()
addPropertyName t i =
  sets_ $ \s -> s { stPropertyNames = (t,i) : stPropertyNames s }

-- | Remember that a source variable got mapped to the given core variable.
rememberMapping :: P.Ident -> C.Ident -> M ()
rememberMapping x y =
  sets_ $ \s -> s { stVarMap = Map.insert x y (stVarMap s) }

getVarMap :: M (Map P.Ident C.Ident)
getVarMap = stVarMap <$> get

--------------------------------------------------------------------------------

-- | Add the type of a binder to the environment.
evalBinder :: P.Binder -> M C.Binder
evalBinder b =
  do c <- case P.binderClock b of
            Nothing -> pure (C.Lit (C.Bool True))
            Just (P.WhenClock _ e i) ->
              do e1 <- evalExprAtom e
                 let i1 = C.Var (evalIdent i)
                 case e1 of
                   C.Lit (C.Bool True) -> pure i1
                   _ -> pure (C.Prim C.Eq [ i1,e1 ])
     let t = evalType (P.binderType b) `C.On` c
     addSrcLocal (P.binderDefines b) t
     let x = P.binderDefines b
         i = evalIdent x
     rememberMapping x i
     pure (i C.::: t)

-- | Translate an equation.
-- Invariant: 'stEqns' should be empty before and after this executes.
evalEqn :: P.Equation -> M [C.Eqn]
evalEqn eqn =
  case eqn of
    P.IsMain _ -> pure []
    P.IVC _    -> pure [] -- XXX: we should do something with these

    P.Property t e -> evalForm "--%PROPERTY" (addPropertyName t) e
    P.Assert t e -> evalForm "assert" (addAssertName t) e

    P.Define ls e ->
      case ls of
        [ P.LVar x ] ->
            do e1  <- evalExpr e
               tys <- getSrcLocalTypes
               let t = case Map.lookup x tys of
                         Just ty -> ty
                         Nothing ->
                            panic "evalEqn" [ "Defining unknown variable:"
                                            , "*** Name: " ++ showPP x ]
               let i = evalIdent x
               addEqn (i C.::: t C.:= e1)
               clearEqns


        _ -> panic "evalExpr"
                [ "Unexpected LHS of equation"
                , "*** Equation: " ++ showPP eqn
                ]

  where
  evalForm :: String -> (C.Ident -> M ()) -> P.Expression -> M [ C.Eqn ]
  evalForm x f e =
    do e1 <- evalExprAtom e
       case e1 of
         C.Var i ->
           do f i
              clearEqns
         C.Lit n ->
          case n of
            C.Bool True  -> pure []
            _ -> panic ("Constant in " ++ x) [ "*** Constant: " ++ show n ]
         C.Prim {} ->
           do C.Var i <- nameExpr (C.Atom e1)
              f i
              clearEqns



-- | Evaluate a source expression to an a core atom, naming subexpressions
-- as needed.
evalExprAtom :: P.Expression -> M C.Atom
evalExprAtom expr =
  do e1 <- evalExpr expr
     case e1 of
       C.Atom a -> pure a
       _        -> nameExpr e1


-- | Evaluate a clock-expression to an atom.
evalClockExprAtom :: P.ClockExpr -> M C.Atom
evalClockExprAtom (P.WhenClock _ e1 i) =
  do a1 <- evalExprAtom e1
     let a2 = C.Var (evalIdent i)
     case a1 of
       C.Lit (C.Bool True) -> pure a2
       _                   -> pure (C.Prim C.Eq [ a1, a2 ])


-- | Translate a source to a core identifier.
evalIdent :: P.Ident -> C.Ident
evalIdent i = C.Ident (P.identText i)


-- | Evaluate a source expression to a core expression.
evalExpr :: P.Expression -> M C.Expr
evalExpr expr =
  case expr of
    P.ERange _ e -> evalExpr e

    P.Var i ->
      do cons <- getEnumCons
         case Map.lookup i cons of
           Just e -> pure e
           Nothing ->
             case i of
               P.Unqual j -> pure (C.Atom (C.Var (evalIdent j)))
               _          -> bad "qualified name"


    P.Lit l -> pure (C.Atom (C.Lit l))

    e `P.When` ce ->
      do a1 <- evalExprAtom e
         a2 <- evalClockExprAtom ce
         pure (C.When a1 a2)


    P.Merge i alts ->
      do let j = C.Var (evalIdent i)
         as <- forM alts $ \(P.MergeCase k e) -> do p  <- evalExprAtom k
                                                    pure (p,e)
         case as of
           [ (C.Lit (C.Bool b) ,e1), (_,e2) ] ->
              do e1' <- evalExprAtom e1
                 e2' <- evalExprAtom e2
                 pure $ if b then C.Merge j e1' e2' else C.Merge j e2' e1'
           _ -> go j as


      where
      go j as =
        case as of
          []  -> bad "empty merge"
          [(_,e)] -> evalExpr e
          (p,e) : rest ->
             do let b = C.Prim C.Eq [ p, j ]
                more <- go j rest
                l    <- evalExprAtom e
                r    <- case more of
                          C.Atom x -> pure x
                          _        -> nameExpr more
                pure (C.Merge b l r)

    P.Tuple {}  -> bad "tuple"
    P.Array {}  -> bad "array"
    P.Select {} -> bad "selection"
    P.Struct {} -> bad "struct"
    P.WithThenElse {} -> bad "with-then-else"

    P.CallPos ni es ->
      do as <- mapM evalExprAtom es
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
                            P.RealCast -> prim C.RealCast
                   _ -> bad "unary operator"

               P.Op2 op2 ->
                 case as of
                   [v1,v2] -> case op2 of
                                P.Fby       -> do v3 <- nameExpr (C.Pre v2)
                                                  pure (v1 C.:-> v3)
                                P.FbyArr    -> pure (v1 C.:-> v2)
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
  bad msg = panic "evalExpr" [ "Unexpected " ++ msg
                             , "*** Expression: " ++ showPP expr
                             ]
