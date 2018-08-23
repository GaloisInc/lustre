{-# Language OverloadedStrings #-}
module Language.Lustre.Transform.NoStatic where

import Data.Text(Text)
import qualified Data.Text as Text
import Data.Map(Map)
import Data.Foldable(foldl')
import qualified Data.Map as Map
import MonadLib

import Language.Lustre.AST
import qualified Language.Lustre.Semantics.Const as C
import Language.Lustre.Semantics.Value
import Language.Lustre.Panic(panic)
import Language.Lustre.Pretty




data Env = Env

  { cEnv :: C.Env
    -- ^ Environment for evaluating constants.

  , enumInfo :: Map Name (Map Ident Name)
    -- ^ For each enum, a map that maps identifiers to the names to
    -- use for the corresponding values.

  , typeAliases :: Map Name Type
    -- ^ Maps type names to evaluated types.
    -- The only named types in an evaluated type are either structs or enums,
    -- there should be no aliases to other types.
    -- We also use this field when we are instantiating a node parameterized
    -- by a type:  the type parameters go in this map, temporarily.

  , nodeTemplates :: Map Name TopDecl
    -- ^ Nodes with static parameters.

  , readyDecls    :: [TopDecl]

  , nodeArgs      :: Map Ident StaticArg
    -- ^ Instantiated node arguments: if the node argument was an instantiation,
    -- then we first instantiate the template, give it a name, and use
    -- that name.  So, we should never have any remaining static
    -- arguments.

  , curModule :: Maybe Text
    -- If this is 'Just', then we use this to qualify top-level
    -- 'Ident' when we need a name 'Name'

  , envNameSeed :: !Int
    -- ^ State used for naming calls to functions with static arguments.

  }


-- | Compute the name for a top-level identifyiner, qualifying with the
-- current module, if any.
topIdentToName :: Env -> Ident -> Name
topIdentToName env i =
  case curModule env of
    Nothing -> Unqual i
    Just m  -> Qual (identRange i) m (identText i)    -- XXX: Pragmas?


-- | Evaluate a constant expression of integer type.
evalIntExpr :: Env -> Expression -> Expression
evalIntExpr env expr =
  case expr of
    ERange r e -> ERange r (evalIntExpr env e)
    _ -> case C.evalIntConst (cEnv env) expr of
           Right i  -> Lit (Int i)
           Left err -> panic "evalIntExpr" [err]

-- | Evaluate a constant expression to a value.
evalExprToVal :: Env -> Expression -> Value
evalExprToVal env expr =
  case expr of
    ERange _ e -> evalExprToVal env e
    _          -> case C.evalConst (cEnv env) expr of
                    Right val -> val
                    Left err  -> panic "evalExprToVal" [err]

-- | Evaluate a constant expression.
evalExpr :: Env -> Expression -> Expression
evalExpr env expr =
  case expr of
    ERange r e -> ERange r (evalExpr env e)
    _          -> valToExpr env (evalExprToVal env expr)

-- | Convert an evaluated expression back into an ordinary expression.
valToExpr :: Env -> Value -> Expression
valToExpr env val =
  case val of
    VInt i        -> Lit (Int i)
    VBool b       -> Lit (Bool b)
    VReal r       -> Lit (Real r)

    VEnum e x ->
      case Map.lookup e (enumInfo env) of
        Just vs ->
          case Map.lookup x vs of
            Just n  -> Var n
            Nothing -> panic "valToExpr"
                        [ "Unknown value of enum `" ++ showPP e ++ "`:"
                        , "*** Value: " ++ showPP x ]
        Nothing -> panic "valToExpr" [ "Unknown enum `" ++ showPP e ++ "`." ]

    VStruct s fs  -> Struct s Nothing
                       [ Field x (valToExpr env v) | (x,v) <- fs ]

    VArray  vs    -> Array (map (valToExpr env) vs)

    VNil          -> panic "valToExpr" ["Unexpected `Nil` value."]



-- | Rewrite an expression that is not neccessarily constant.
evalDynExpr :: Env -> Expression -> M Expression
evalDynExpr env expr =
  case expr of
    ERange r e      -> ERange r <$> evalDynExpr env e
    Var x           -> pure $ case Map.lookup x (C.envConsts (cEnv env)) of
                                Just v -> valToExpr env v
                                Nothing -> expr
    Lit _           -> pure expr
    EOp1 op e       -> EOp1 op <$> evalDynExpr env e
    EOp2 e1 op e2   -> do e1' <- evalDynExpr env e1
                          e2' <- evalDynExpr env e2
                          pure (EOp2 e1' op e2')
    e1 `When` e2    -> do e1' <- evalDynExpr env e1
                          pure (e1' `When` evalClockExpr env e2)
    EOpN op es      -> EOpN op <$> mapM (evalDynExpr env) es
    Tuple es        -> Tuple <$> mapM (evalDynExpr env) es
    Array es        -> Array <$> mapM (evalDynExpr env) es
    Select e s      -> do e' <- evalDynExpr env e
                          pure (Select e' (evalSel env s))

    Struct s mb fs  -> undefined


    IfThenElse e1 e2 e3 ->
      IfThenElse <$> evalDynExpr env e1 <*>
                     evalDynExpr env e2 <*> evalDynExpr env e3


    WithThenElse e1 e2 e3 ->
      case evalExprToVal env e1 of
        VBool b -> evalDynExpr env (if b then e2 else e3)
        v       -> panic "evalDynExpr"
                      [ "Decision in `with-then-else` is not a `bool`"
                      , "*** Value: " ++ showPP (valToExpr env v)
                      ]

    Merge i ms -> undefined

    CallPos f es ->
      do es' <- mapM (evalDynExpr env) es
         case f of
           NodeInst c [] -> pure (resolvePlainCall env c es')
           _ -> do f'  <- nameInstance env f
                   pure (CallPos f' es')

resolvePlainCall :: Env -> Callable -> [ Expression ] -> Expression
resolvePlainCall env c es =
  case c of
    CallUser (Unqual i)
      | Just def <- Map.lookup i (nodeArgs env) ->
        case def of
          _ -> undefined
    _ -> CallPos (NodeInst c []) es


nameInstance :: Env -> NodeInst -> M NodeInst
nameInstance env (NodeInst fu xs) =
  case xs of
    [] -> pure (NodeInst fu xs)
    _  -> do ys <- mapM (evalStaticArg env) xs
             g  <- addNameInstDecl fu ys
             pure (NodeInst (CallUser g) [])

evalStaticArg :: Env -> StaticArg -> M StaticArg
evalStaticArg env sa =
  case sa of
    ArgRange r sa1  -> ArgRange r <$> evalStaticArg env sa1
    NodeArg fu ni   -> NodeArg fu <$> nameInstance env ni

    TypeArg t       -> pure (TypeArg (evalType env t))
    ExprArg e       -> pure (ExprArg (evalExpr env e))
    Op1Arg _        -> pure sa
    Op2Arg _        -> pure sa
    OpIf            -> pure sa



-- | Evaluate a selector.  The indixes in a selector are constants.
evalSel :: Env -> Selector Expression -> Selector Expression
evalSel env sel =
  case sel of
    SelectField i   -> SelectField i
    SelectElement e -> SelectElement (evalIntExpr env e)
    SelectSlice s   -> SelectSlice (evalSlice env s)

-- | Eval an array slice.  The indexes in the slice are constants.
evalSlice :: Env -> ArraySlice Expression -> ArraySlice Expression
evalSlice env s = ArraySlice { arrayStart = evalIntExpr env (arrayStart s)
                             , arrayEnd   = evalIntExpr env (arrayEnd s)
                             , arrayStep  = evalIntExpr env <$> arrayStep s
                             }

-- | Evaluate a type: resolves named types, and evaluates array sizes.
evalType :: Env -> Type -> Type
evalType env ty =
  case ty of
    TypeRange r t -> TypeRange r (evalType env t)

    ArrayType t e -> ArrayType   (evalType env t) (evalIntExpr env e)

    -- XXX: Are the locations in the aliased type meaningful?
    NamedType n   -> case Map.lookup n (typeAliases env) of
                       Just t1 -> t1
                       Nothing -> NamedType n

    IntType       -> IntType
    RealType      -> RealType
    BoolType      -> BoolType


-- | Evaluate a type declarations.
evalTypeDecl :: Env -> TypeDecl -> Env
evalTypeDecl env td =
  case typeDef td of
    Nothing -> panic "evalTypeDecls" [ "Unsupported abstract type:"
                                     , "*** Name: " ++ showPP name
                                     ]
    Just tdef ->
      case tdef of
        IsType x -> addAlias env name (evalType env x)
        IsEnum xs ->
          let ys = Map.fromList [ (x, topIdentToName env x) | x <- xs ]
          in env { enumInfo = Map.insert name ys (enumInfo env) }
        IsStruct xs ->
          let (fs,ds) =
                unzip [ ( (fieldName x, evalExprToVal env <$> fieldDefault x)
                        , x { fieldType = evalType env (fieldType x)
                            , fieldDefault = Nothing
                            }
                        ) | x <- xs ]
              update cenv =
                cenv { C.envStructs = Map.insert name fs (C.envStructs cenv) }
          in env { cEnv = update (cEnv env)
                 , readyDecls = DeclareType td { typeDef = Just (IsStruct ds) }
                              : readyDecls env
                 }
  where
  name = topIdentToName env (typeName td)


-- | Add a new name for the given type.  If the named type is a struct or
-- an enum, then also add propriate entries to the other maps,
-- so we can do direct look-ups without having to consult the alias map.
addAlias :: Env -> Name -> Type -> Env
addAlias env x t =
  case t of
    NamedType n ->
      case Map.lookup n (enumInfo env) of
        Just i -> env1 { enumInfo = Map.insert x i (enumInfo env1) }
        Nothing ->
          let cenv = cEnv env
          in case Map.lookup n (C.envStructs cenv) of
               Just i ->
                 let newMap = Map.insert x i (C.envStructs cenv)
                 in env1 { cEnv = cenv { C.envStructs = newMap } }
               Nothing -> panic "addAlias"
                            [ "Named type is neither `enum`, nor `struct`:"
                            , "*** Name: " ++ showPP n
                            ]
    _ -> env1
  where
  env1 = env { typeAliases = Map.insert x t (typeAliases env) }


-- | Evaluate the definition of a constant, adding its values to the
-- environment.
evalConstDef :: Env -> ConstDef -> Env
evalConstDef env cd = env { cEnv = newCEnv }
  where
  cenv    = cEnv env
  val     = case constDef cd of
              Just e -> evalExprToVal env e
              Nothing -> panic "evalConstDef"
                           [ "Uninterpreted constants are not supported."
                           , "*** Name: " ++ showPP (constName cd)
                           ]
  -- XXX: Should we be using qualified or unqualified names here?
  newCEnv = cenv { C.envConsts = Map.insert (Unqual (constName cd)) val
                                            (C.envConsts cenv) }


-- | Evaluate a clock expression.  The value activating the clock
-- is a constnat, and the identifier is definatly not.
evalClockExpr :: Env -> ClockExpr -> ClockExpr
evalClockExpr env (WhenClock r e i) = WhenClock r (evalExpr env e) i

-- | Evaluate a binder.have been evaluated already.
evalBinder :: Env -> Binder -> Binder
evalBinder env b = b { binderType = evalType env (binderType b)
                     , binderClock = evalClockExpr env <$> binderClock b
                     }

-- | Remove the given identivier from the constant environment,
-- as it is shadowed by a local variable.
shadowIdent :: Env -> Ident -> Env
shadowIdent env i = env { cEnv = update (cEnv env) }
  where
  update cenv = cenv { C.envConsts = Map.delete (Unqual i) (C.envConsts cenv) }

-- | Remove a whole bunch of binders.
shadowBinders :: Env -> [Binder] -> Env
shadowBinders = foldr (\b e -> shadowIdent e (binderDefines b))

-- | Evaluate a bunch of locals:  the constants are added to the environment,
-- and we get the binders for the variables.
evalLocalDecls :: Env -> [ LocalDecl ] -> ([Binder], Env)
evalLocalDecls env ds = ( [ evalBinder env1 b | LocalVar b <- ds ]
                        , env1
                        )
  where
  env1 = foldl' evalConstDef env [ c | LocalConst c <- ds ]

-- | Evaluate the binders in the type of a node.
evalNodeProfile :: Env -> NodeProfile -> NodeProfile
evalNodeProfile env np =
  NodeProfile { nodeInputs  = map (evalBinder env) (nodeInputs np)
              , nodeOutputs = map (evalBinder env) (nodeOutputs np)
              }

-- | Evaluate an equation.
evalEqn :: Env -> Equation -> M Equation
evalEqn env eqn =
  case eqn of
    Assert e -> Assert <$> evalDynExpr env e
    Define ls e -> Define (map (evalLHS env) ls) <$> evalDynExpr env e

-- | Evaluate a left-hand-side of an equation.
evalLHS :: Env -> LHS Expression -> LHS Expression
evalLHS env lhs =
  case lhs of
    LVar x      -> LVar x
    LSelect l s -> LSelect (evalLHS env l) (evalSel env s)

-- | Evaluate a node with the given static parameters.
-- We assume that the arguments have been evaluated already.
evalNode :: Env -> NodeDecl -> [StaticArg] -> Env
evalNode env nd args =
  case nodeDef nd of
    Nothing -> panic "evalNode" [ "Node without a definition"
                                , "*** Name: " ++ showPP (nodeName nd)
                                ]
    Just body ->
      env { readyDecls = DeclareNode newNode : map DeclareNodeInst insts
                                                            ++ readyDecls env
          , envNameSeed = newS
          }
      where
      prof      = nodeProfile nd
      env0      = addStaticParams (nodeStaticInputs nd) args env
      env1      = shadowBinders env0 (nodeInputs prof)
      (bs,env2) = evalLocalDecls env1 (nodeLocals body)
      env3      = shadowBinders (shadowBinders env2 bs) (nodeOutputs prof)
      env4      = env3 { envNameSeed = panic "evalNode"
                          [ "[bug] Incorrect use of `envNameSeed`" ] }
      (eqs,insts,newS) = runNameStatic
                           (curModule env4)
                           (envNameSeed env)
                           (mapM (evalEqn env4) (nodeEqns body))


      newName   = case args of
                    [] -> nodeName nd
                    _  -> undefined -- XXX

      newDef    = NodeBody
                    { nodeLocals = map LocalVar bs
                    , nodeEqns   = eqs
                    }

      newNode   = nd { nodeName = newName
                     , nodeStaticInputs = []
                     , nodeProfile = evalNodeProfile env0 (nodeProfile nd)
                     , nodeDef = Just newDef
                    }

-- For now don't instantiate nodes, just rememebr templates
evalNodeDecl :: Env -> NodeDecl -> Env
evalNodeDecl env nd =
  case nodeStaticInputs nd of
    [] -> evalNode env nd []
    _  -> env { nodeTemplates = Map.insert name (DeclareNode nd)
                                                (nodeTemplates env) }
  where
  name = topIdentToName env (nodeName nd)


addStaticParam :: StaticParam -> StaticArg -> Env -> Env
addStaticParam p a env =
  case (p,a) of

    (_, ArgRange _ a1) -> addStaticParam p a1 env -- XXX: use location!

    (TypeParam i, TypeArg t) ->
      env { typeAliases = Map.insert (Unqual i) t (typeAliases env) }

    (TypeParam i, _) ->
      panic "addStaticParam"
        [ "Invalid static parameter:"
        , "*** Expected: a type for " ++ showPP i
        , "*** Got: " ++ showPP a
        ]



    (ConstParam i _, ExprArg e) ->
      let cenv   = cEnv env
          val    = evalExprToVal env e
      in env { cEnv = cenv { C.envConsts = Map.insert (Unqual i) val
                                                    (C.envConsts cenv) } }
    (ConstParam c t, _) ->
      panic "addStaticParam"
        [ "Invalid static parameter:"
        , "*** Expected: a constant " ++ showPP c ++ " : " ++ showPP t
        , "*** Got: " ++ showPP a
        ]

    (NodeParam _ _ f _, _) ->
        env { nodeArgs = Map.insert f a (nodeArgs env) }


addStaticParams :: [ StaticParam ] -> [ StaticArg ] -> Env -> Env
addStaticParams ps as env =
  case (ps,as) of
    ([], []) -> env
    (p : ps1, a : as1) -> addStaticParams ps1 as1 (addStaticParam p a env)
    _ -> panic "addStaticParams" [ "Mismatch in static aruments" ]

-- | The arguments are assumed to have been evaluated already
evalNodeInst :: Env -> NodeInstDecl -> [StaticArg] -> Env
evalNodeInst env nid args =
  env { readyDecls  = map DeclareNodeInst (newInst : insts) ++ readyDecls env
      , envNameSeed = newS
      }
  where
  env0 = addStaticParams (nodeInstStaticInputs nid) args env
  env1 = env0 { envNameSeed = panic "evalNodeInst"
                                [ "[bug] Incorrect use of `envNameSeed`" ] }

  nameNodeInstDef (NodeInst f as) =
    case as of
      [] | CallUser (Unqual fu) <- f
         , Just def <- Map.lookup fu (nodeArgs env1) ->
            case def of
              NodeArg _ n -> pure n
              _ -> undefined -- XXX: we don't support operators for the moment


      _  -> do bs <- mapM (evalStaticArg env1) as
               pure (NodeInst f bs)

  (newDef,insts,newS) = runNameStatic
                            (curModule env1)
                            (envNameSeed env)
                            (nameNodeInstDef (nodeInstDef nid))


  newName   = case args of
                    [] -> nodeInstName nid
                    _  -> undefined -- XXX

  newInst = nid { nodeInstName         = newName
                , nodeInstStaticInputs = []
                , nodeInstProfile      = Nothing -- XXX: do we need this?
                , nodeInstDef          = newDef
                }


evalNodeInstDecl :: Env -> NodeInstDecl -> Env
evalNodeInstDecl env nid =
  case nodeInstStaticInputs nid of
    [] -> evalNodeInst env nid []
    _  -> env { nodeTemplates = Map.insert name (DeclareNodeInst nid)
                                                (nodeTemplates env) }
  where
  name = topIdentToName env (nodeInstName nid)

nsTopDecl :: Env -> TopDecl -> Env
nsTopDecl env td =
  case td of
    DeclareType tde     -> evalTypeDecl env tde
    DeclareConst cd     -> evalConstDef env cd
    DeclareNode nd      -> evalNodeDecl env nd
    DeclareNodeInst nid -> evalNodeInstDecl env nid


--------------------------------------------------------------------------------
type M = ReaderT RO (StateT RW Id)

runNameStatic ::
  Maybe Text {- ^ Qualify generated names with this -} ->
  Int        {- ^ Start generating names using this seed -} ->
  M a        {- ^ This is what we want to do -} ->
  (a, [ NodeInstDecl ], Int) -- ^ result, new instances, new name seed
runNameStatic qual seed m = (a, reverse (instances rw1), nameSeed rw1)
  where
  (a,rw1) = runId $ runStateT rw $ runReaderT ro m
  ro      = RO { qualify = qual }
  rw      = RW { nameSeed = seed, instances = [] }

newtype RO = RO
  { qualify :: Maybe Text             -- ^ Qualify references to generated names
  }

data RW = RW
  { nameSeed    :: !Int               -- ^ Generate new names
  , instances   :: [ NodeInstDecl ]   -- ^ Generated declarations
  }


{- | Name the given instantiation.
XXX: For the moment, all new nodes are "safe nodes".
Eventually, we should probably be more accurate and keep track of the
safety & functionality of declarations.
-}
addNameInstDecl :: Callable -> [StaticArg] -> M Name
addNameInstDecl c as =
  do i <- newIdent (range c)
     addInst NodeInstDecl
                { nodeInstSafety        = Safe
                , nodeInstType          = Node
                , nodeInstName          = i
                , nodeInstStaticInputs  = []
                , nodeInstProfile       = Nothing
                , nodeInstDef           = NodeInst c as
                }
     identToName i

-- | Generate a fresh name associated with the given source location.
newIdent :: SourceRange -> M Ident
newIdent r = sets $ \s -> let x = nameSeed s
                              newName = "__no_static_" <> Text.pack (show x)
                              i = Ident { identRange = r
                                        , identText = newName
                                        , identPragmas = []
                                        }
                              s1 = s { nameSeed = x + 1 }
                          in s1 `seq` (i, s1)

-- | Convert an identifier to a name, by qualifying it, if neccesary.
identToName :: Ident -> M Name
identToName i =
  do mbQ <- asks qualify
     pure $ case mbQ of
              Nothing -> Unqual i
              Just q  -> Qual (identRange i) q (identText i)

-- | Remember the given instance.
addInst :: NodeInstDecl -> M ()
addInst ni = sets_ $ \s -> s { instances = ni : instances s }


