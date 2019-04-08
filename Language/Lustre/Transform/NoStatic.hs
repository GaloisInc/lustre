{-# Language OverloadedStrings, DataKinds #-}
{-| NOTE: At the moment the transformation in this pass are not really
optional, as the following passes expect them.

XXX: This is quite comples, and it should probably be split into
the code that names call sites, and the code that actually instantiates
static parameters.

This module removes static arguments and constants.
Calls to functions with static arguments are lifted to the top-level
and given an explicit name.

Also, in this pass we desugar calls to `condact`

Optionally (flag 'expandNodeInstDecl'), we can also expand functions
applied to static arguments to functions using a specialized definition instead.

Optionally (flag 'nameCallSites), we can add explicit names for nested call
sites.  For example, if @f(x,y)@ is a call that appears somewhere in an
expression, we add a new equation:

p,q,r = f (x,y)

and replace the function call with @(p,q,r)@.

This will help with the following transformations:

  1. when removing structured data, it is convenient if structured data is
     either explicit or a variable:  we can work around that for "simple"
     expressions such as "when" and "merge", however we don't want to
     duplicate function calls, so naming them is useful.

  2. if function calls are named, it should be simpler to inline the
     function's definition, as we can use the equations from `f` to
     define `p`, `q`, and `r`.

NOTE: We do NOT name calls to primitives that return a single result
(e.g., +, #, |, or ITE)
-}

module Language.Lustre.Transform.NoStatic
  ( noConst
  , CallSiteMap
  , CallSiteId, idFromRange, callSiteName
  ) where

import Data.Function(on)
import Data.Either(partitionEithers)
import Data.Map(Map)
import Data.Foldable(foldl')
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import MonadLib
import Text.PrettyPrint(punctuate,comma,hsep)

import Language.Lustre.AST
import Language.Lustre.Monad
import qualified Language.Lustre.Semantics.Const as C
import Language.Lustre.Semantics.Value
import Language.Lustre.Panic(panic)
import Language.Lustre.Pretty

-- | Currently assumes an empty environment.
noConst :: [TopDecl] -> LustreM (CallSiteMap, [TopDecl])
noConst ds =
  do seed <- getNameSeed
     let env = evalTopDecls (emptyEnv seed)
                { expandNodeInsts = True
                , nameCallSites   = True
                , envCurMod       = Nothing
                } ds
     setNameSeed (envNameInstSeed env)
     pure (envCallSiteMap env, reverse (readyDecls env))


-- | Evaluate a top-level declaration.
evalTopDecl :: Env -> TopDecl -> Env
evalTopDecl env td =
  case td of
    DeclareType tde     -> evalTypeDecl env tde
    DeclareConst cd     -> evalConstDef env cd
    DeclareNode nd      -> evalNodeDecl env nd
    DeclareNodeInst nid -> evalNodeInstDecl env nid

-- | Evaluate multiple top-level declarations from the same modeule.
evalTopDecls :: Env -> [TopDecl ] -> Env
evalTopDecls = foldl' evalTopDecl


-- | Maps node definitions to the places in the source where they are called.
-- For each call, we keep track of the left-hand-sides storing the results
-- of the call.
type CallSiteMap = Map OrigName (Map CallSiteId [LHS Expression])

-- | Identifies a call site uniquely.
-- Currently, it is computed from the location in the source.
-- XXX: Needs to be augmented to support multiple files/modules.
data CallSiteId = CallSiteId { csId :: (Int,Int), csRange :: SourceRange }
                  deriving (Show)

-- | An identifer for a call site.  This is computed from the location in the
-- source and so it should be unique wrt to a file, but not when multiple
-- file are involved.
callSiteName :: CallSiteId -> String
callSiteName x = "cs_" ++ show a ++ "_" ++ show b
  where (a,b) = csId x

instance HasRange CallSiteId where
  range = csRange

instance Eq CallSiteId where
  (==) = (==) `on` csId

instance Ord CallSiteId where
  compare = compare `on` csId

-- | This ignores files, so it only makes sense for ranges in the same file.
idFromRange :: SourceRange -> CallSiteId
idFromRange r = CallSiteId { csId    = (pos sourceFrom, pos sourceTo)
                           , csRange = r }
  where
  pos f = sourceIndex (f r)


--------------------------------------------------------------------------------
-- Evaluation Context and State



data Env = Env

  { cEnv :: C.Env
    -- ^ Environment for evaluating constants.

  , nodeInfo :: Map OrigName NodeProfile
    -- ^ Types of the nodes that are in scope.
    -- This is used to determine how to name the call sites.
    -- It is also used to figure out which parameters are constants
    -- when we call a function.

  , nodeTemplates :: Map OrigName TopDecl
    -- ^ Nodes with static parameters, used when we expand definitions.
    -- These declarations are NOT evaluated, instead we make a new copy
    -- for each instantiation.

  , typeAliases :: Map OrigName Type
    -- ^ Maps type names to evaluated types.
    -- The only named types in an evaluated type are either structs or enums,
    -- there should be no aliases to other types.
    -- We also use this field when we are instantiating a node parameterized
    -- by a type:  the type parameters go in this map, temporarily.

  , envCurMod :: Maybe ModName
    -- ^ Use this in the original name, when generating fresh top-level names.
    -- (e.g., for naming instantiate things, or call sites).

  , expandNodeInsts :: Bool
    {- ^ Should we expand node instances, or leave them named at the
        top level.  Note that we don't do any sharing at the moment,
        so multiple identical instantiations would be simply copies
        of each other.
        NOTE: Later passes assumes that this is True
    -}

  , nameCallSites :: Bool
    {- ^ Should we add explicit equations for each call site?
       NOTE: Later passes assume that this is True
    -}

  , envNameInstSeed :: !NameSeed
    -- ^ For generating names for function instantiations (not-expanded)

  , envCurRange :: Maybe SourceRange
    -- ^ Whereabouts are we

  , readyDecls    :: [TopDecl]
    -- ^ Declarations that we've already processed.
    -- These are the output of the algorithm.

  , nodeArgs      :: Map OrigName NodeInst
    -- ^ Instantiated node arguments: if the node argument was an instantiation,
    -- then we first instantiate the template, give it a name, and use
    -- that name.  So, we should never have any remaining static
    -- arguments.


  , envCallSiteMap :: CallSiteMap
    {- ^ For each node, maps a range in the source to a call site.
    The call site is identified by the variables storing the results
    of the call.  This is useful so that we can propagate results from
    later passes back to the calls they correspond to.
    -}

  }

inRange :: SourceRange -> Env -> Env
inRange r env = env { envCurRange = Just r }


-- | Does not expand node instances
emptyEnv :: NameSeed -> Env
emptyEnv seed =
  Env { cEnv = C.emptyEnv
      , nodeInfo = Map.empty
      , typeAliases = Map.empty
      , nodeTemplates = Map.empty
      , readyDecls = []
      , nodeArgs = Map.empty
      , expandNodeInsts = False
      , nameCallSites = False
      , envNameInstSeed = seed
      , envCurRange = Nothing
      , envCallSiteMap = Map.empty
      , envCurMod = Nothing
      }

lookupNodeTemplateInfo ::
  OrigName -> Env -> Maybe ([StaticParam], Either NodeProfile NodeInst)
lookupNodeTemplateInfo x env =
  do temp <- Map.lookup x (nodeTemplates env)
     case temp of
       DeclareNode nd -> pure ( nodeStaticInputs nd ++ getConstParams p
                              , Left p
                              )
         where p = nodeProfile nd

       DeclareNodeInst nid ->
         pure (nodeInstStaticInputs nid, Right (nodeInstDef nid))
       it -> panic "lookupNodeTemplateInfo"
               [ "Unexpected template for " ++ showPP x
               , "*** Declaration:"
               , showPP it
               ]

getConstParams :: NodeProfile -> [ StaticParam ]
getConstParams p = [ ConstParam i t | InputConst i t <- nodeInputs p ]


--------------------------------------------------------------------------------
-- Evaluation of types

-- | Evaluate a type declaration.
evalTypeDecl :: Env -> TypeDecl -> Env
evalTypeDecl env td =
  case typeDef td of
    Nothing -> panic "evalTypeDecls" [ "Unsupported abstract type:"
                                     , "*** Name: " ++ showPP name
                                     ]
    Just tdef ->
      case tdef of
        IsType x -> addAlias env name (evalType env x)

        -- Add the enumeration constants to the constant environemnt.
        IsEnum xs -> env { cEnv = update (cEnv env) }
          where
          update cenv =
                 cenv { C.envConsts = foldr addVal (C.envConsts cenv) xs }
          addVal i = let nm = identOrigName i
                     in Map.insert nm (VEnum name nm)

        IsStruct xs ->
          env { cEnv = update (cEnv env)
              , readyDecls = DeclareType td { typeDef = Just (IsStruct ds) }
                           : readyDecls env
              }
          where
          update cenv =
            cenv { C.envStructs = Map.insert name fs (C.envStructs cenv) }

          (fs,ds) = unzip (map doField xs)

          doField x =
            ( (fieldName x, evalExprToVal env <$> fieldDefault x)

              , x { fieldType = evalType env (fieldType x)
                  , fieldDefault = Nothing
                  }
            )

  where
  name = identOrigName (typeName td)



-- | Evaluate a type: resolves named types, and evaluates array sizes.
evalType :: Env -> Type -> Type
evalType env ty =
  case ty of
    TypeRange r t -> TypeRange r (evalType env t)

    ArrayType t e -> ArrayType   (evalType env t) (evalIntExpr env e)

    IntSubrange e1 e2 -> IntSubrange (evalIntExpr env e1) (evalIntExpr env e2)

    -- XXX: Note that the locations in the expanded type will be those
    -- of the definition site, not the ones at the use site.
    NamedType n   -> case Map.lookup (nameOrigName n) (typeAliases env)  of
                       Just t1 -> t1
                       Nothing -> NamedType n

    IntType       -> IntType
    RealType      -> RealType
    BoolType      -> BoolType
    TVar x        -> panic "evalType" [ "Unexpected type variable"
                                      , "*** Tvar: " ++ showPP x ]



-- | Add a new name for the given type.  If the named type is a struct,
-- then also add appropriate entries to the other maps,
-- so we can do direct look-ups without having to consult the alias map.
addAlias :: Env -> OrigName -> Type -> Env
addAlias env x t =
  case t of
    NamedType n ->
      case checkEnum `mplus` checkStruct of
        Just env2 -> env2
        Nothing  -> panic "addAlias"
                      [ "Named type is neither `enum`, nor `struct`:"
                      , "*** Name: " ++ showPP n
                      ]
      where
      checkEnum = pure env1

      checkStruct =
        do let cenv = cEnv env
           i <- Map.lookup (nameOrigName n) (C.envStructs cenv)
           let newMap = Map.insert x i (C.envStructs cenv)
           pure env1 { cEnv = cenv { C.envStructs = newMap } }

    _ -> env1
  where
  env1 = env { typeAliases = Map.insert x t (typeAliases env) }




--------------------------------------------------------------------------------
-- Evaluation of constants

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

  newCEnv = cenv { C.envConsts = Map.insert name val (C.envConsts cenv) }
  name    = identOrigName (constName cd)



-- | Evaluate a constant expression of integer type.
evalIntExpr :: Env -> Expression -> Expression
evalIntExpr env expr =
  case expr of
    ERange r e -> ERange r (evalIntExpr (inRange r env) e)
    _ -> case C.evalIntConst (cEnv env) expr of
           Right i  -> Lit (Int i)
           Left err -> panic "evalIntExpr" [err]

-- | Evaluate a constant expression to a value.
evalExprToVal :: Env -> Expression -> Value
evalExprToVal env expr =
  case expr of
    ERange r e -> evalExprToVal (inRange r env) e
    _          -> case C.evalConst (cEnv env) expr of
                    Right val -> val
                    Left err  -> panic "evalExprToVal" [err]

-- | Evaluate a constant expression.
evalExpr :: Env -> Expression -> Expression
evalExpr env expr =
  case expr of
    ERange r e -> ERange r (evalExpr (inRange r env) e)
    _          -> valToExpr (evalExprToVal env expr)

-- | Convert an evaluated expression back into an ordinary expression.
-- Note that the resulting expression does not have meaninful position
-- information.
valToExpr :: Value -> Expression
valToExpr val =
  case val of
    VInt i        -> Lit (Int i)
    VBool b       -> Lit (Bool b)
    VReal r       -> Lit (Real r)

    -- we keep enums as variables, leaving representation choice for later.
    VEnum _ x     -> Var (origNameToName x)
    VStruct s fs  -> Struct (origNameToName s) (fmap (fmap valToExpr) fs)

    VArray  vs    -> Array (map valToExpr vs)


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

-- | Evaluate a clock expression.  The value activating the clock
-- is a constnat, and the identifier is definatly not.
evalClockExpr :: Env -> ClockExpr -> ClockExpr
evalClockExpr env (WhenClock r e i) = WhenClock r (evalExpr env e) i

evalCType :: Env -> CType -> CType
evalCType env ct = CType { cType = evalType env (cType ct)
                         , cClock = evalIClock env (cClock ct)
                         }

evalIClock :: Env -> IClock -> IClock
evalIClock env clk =
  case clk of
    BaseClock -> BaseClock
    KnownClock c -> KnownClock (evalClockExpr env c)
    ClockVar {} -> panic "NoStatic.evalIClock" [ "Unexpected clock variable." ]



--------------------------------------------------------------------------------
-- Evaluation of Nodes


{- | Evaluate a node declaration.
Nodes with static parameters are added to the template map, while "normal"
nodes are evaluated and added to the declaration list. -}
evalNodeDecl :: Env -> NodeDecl  -> Env
evalNodeDecl env nd =
  case nodeStaticInputs nd ++ getConstParams (nodeProfile nd) of
    [] -> evalNode env nd []
    ps -> env { nodeTemplates = Map.insert name (DeclareNode nd)
                                                (nodeTemplates env)
              , nodeInfo = Map.insert name (nodeProfile nd) (nodeInfo env)
              }
  where
  name    = identOrigName (nodeName nd)


-- | Evaluate and instantiate a node with the given static parameters.
-- We assume that the arguments have been evaluated already.
evalNode :: Env -> NodeDecl -> [StaticArg] -> Env
evalNode env nd args =

  case nodeDef nd of
    -- XXX
    Nothing -> panic "evalNode" [ "Not yet implemented:"
                                , "*** Node without a definition"
                                , "*** Name: " ++ showPP (nodeName nd)
                                ]
    Just body ->
         envRet2 { readyDecls = DeclareNode newNode : readyDecls envRet2
                 , nodeInfo   = Map.insert name newProf (nodeInfo envRet2)
                 }
      where
      name      = identOrigName (nodeName nd)

      -- 1. bind the provided static arguments.
      env0      = addStaticParams (nodeStaticInputs nd) args env
      newProf   = evalNodeProfile env0 (nodeProfile nd)

      -- 2. evaluate constants in the locals
      (bs,env1) = evalLocalDecls env0 (nodeLocals body)

      -- 3. "blackhole" the name seed, which should not be used.
      -- This a strict field, so we can't put a panic there, so instead
      -- we just make up a very invalid value, which would hopefully be
      -- easy to spot, in case it get used accidentally.
      env2      = env1 { envNameInstSeed = invalidNameSeed 77 }

      -- 4. Evaluate the equations in the body of a node.
      (eqs,newLs,insts,info,newS) =
          runNameStatic (envNameInstSeed env)
                        (envCurMod env)
                        (concat <$> mapM (evalEqn env2) (nodeEqns body))

      -- Results, updating the *original* environment.
      envRet1 = env { envNameInstSeed = newS
                    , envCallSiteMap = Map.insert name info (envCallSiteMap env)
                    }
      envRet2 = addEvaluatedNodeInsts envRet1 insts


      newDef    = NodeBody
                    { nodeLocals = map LocalVar (newLs ++ bs)
                    , nodeEqns   = eqs
                    }

      newNode   = nd { nodeStaticInputs = []
                     , nodeProfile = newProf
                     , nodeDef = Just newDef
                    }




-- | Evaluate a binder.have been evaluated already.
evalBinder :: Env -> Binder -> Binder
evalBinder env b = b { binderType = evalType env (binderType b)
                     , binderClock = evalClockExpr env <$> binderClock b
                     }


-- | Evaluate the binders in the type of a node.
evalNodeProfile :: Env -> NodeProfile -> NodeProfile
evalNodeProfile env np =
  NodeProfile { nodeInputs  = map (evalInputBinder env) (nodeInputs np)
              , nodeOutputs = map (evalBinder env) (nodeOutputs np)
              }


evalInputBinder :: Env -> InputBinder -> InputBinder
evalInputBinder env ib =
  case ib of
    InputBinder b -> InputBinder (evalBinder env b)
    InputConst i t -> panic "evalInputBinder"
                        [ "Unexpected constant parameter."
                        , "It should have been desugared by now."
                        , "*** Name: " ++ showPP i
                        , "*** Type: " ++ showPP t ]


-- | Evaluate a bunch of locals:  the constants are added to the environment,
-- and we get the binders for the variables.
evalLocalDecls :: Env -> [ LocalDecl ] -> ([Binder], Env)
evalLocalDecls env ds = ( [ evalBinder env1 b | LocalVar b <- ds ]
                        , env1
                        )
  where
  env1 = foldl' evalConstDef env [ c | LocalConst c <- ds ]

{-
evalContractItems env cis = undefined
  where
  consts = [ (c,e) | GhostConst c _ e <- cis ]
  evalC env (c,e) = let v = evalExprToVal env e
                        n = Unqual Ghost c
                    in env { 

-- | Assumes that ghost variables have been ordered.
evalContractItem :: Env -> ContractItem -> M [ContractItem]
evalContractItem env ci =
  case ci of
    GhostConst c mbT e -> GhostConst c 
    GhostVar   b e     ->
    Assume e           ->
    Guarantee e        ->
    Mode m as ts       ->
    Import c is os     ->
-}

-- | Evaluate an equation.
evalEqn :: Env -> Equation -> M [Equation]
evalEqn env eqn =
  collectFunEqns $
  case eqn of
    Assert x e    -> Assert x <$> evalDynExpr NestedExpr env e
    Property x e  -> Property x <$> evalDynExpr NestedExpr env e
    Define ls e   -> let lhs = map (evalLHS env) ls
                     in Define lhs <$> evalDynExpr (TopExpr lhs) env e
    IsMain r      -> pure (IsMain r)
    IVC is        -> pure (IVC is)

-- | Evaluate a left-hand-side of an equation.
evalLHS :: Env -> LHS Expression -> LHS Expression
evalLHS env lhs =
  case lhs of
    LVar x      -> LVar x
    LSelect l s -> LSelect (evalLHS env l) (evalSel env s)


--------------------------------------------------------------------------------
-- Evaluating and Expanding Node Instances

-- | Evaluate a node-instance declaration.
-- Parameterized ones are added to the template map.
evalNodeInstDecl :: Env -> NodeInstDecl -> Env
evalNodeInstDecl env nid =
  case nodeInstStaticInputs nid of
    [] -> evalNodeInst env nid []
    ps -> env { nodeTemplates = Map.insert name (DeclareNodeInst nid)
                                                (nodeTemplates env)
              }
  where
  name = identOrigName (nodeInstName nid)


-- | Evaluate a node-instance declaration using the given static arguments.
-- The static arguments should have been evaluated already.
evalNodeInst :: Env -> NodeInstDecl -> [StaticArg] -> Env
evalNodeInst env nid args = addEvaluatedNodeInst envRet2 newInst
  where
  env0 = addStaticParams (nodeInstStaticInputs nid) args env
  env1 = env0 { envNameInstSeed = invalidNameSeed 78 }
            -- Do not use! Bogus value for sanity.
            -- (strict, so no error/undefined)

  nameNodeInstDef (NodeInst f as) =
    case as of
      [] | CallUser nm <- f
         , Just ni <- Map.lookup (nameOrigName nm) (nodeArgs env1) -> pure ni
      _  -> do bs <- mapM (evalStaticArg env1) as
               pure (NodeInst f bs)

  (newDef,[],insts,info,newS) = runNameStatic
                                (envNameInstSeed env)
                                (envCurMod env)
                                (nameNodeInstDef (nodeInstDef nid))

  envRet1 = env { envNameInstSeed = newS
                , envCallSiteMap =
                    let nm = identOrigName (nodeInstName nid)
                    in Map.insert nm info (envCallSiteMap env) }
  envRet2 = addEvaluatedNodeInsts envRet1 insts

  -- Note that we leave the name as is because this is the right thing
  -- for nodes with no static parameters.   If, OTOH, we are instantiating
  -- a template, then we've already put the correct name in the template.

  newInst = nid { nodeInstStaticInputs = []
                , nodeInstProfile      = Nothing
                , nodeInstDef          = newDef
                }




-- | Add an already evaluated node instance to the environment.
-- This is where we expand instances, if the flag in the environment is set.
addEvaluatedNodeInst :: Env -> NodeInstDecl -> Env
addEvaluatedNodeInst env ni
  | expandNodeInsts env = expandNodeInstDecl env ni
  | otherwise           = doAddNodeInstDecl ni env

-- | Add an already evaluated node instance to the environment.
-- This is where we expand instances, if the flag in the environment is set.
addEvaluatedNodeInsts :: Env -> [NodeInstDecl] -> Env
addEvaluatedNodeInsts = foldl' addEvaluatedNodeInst

-- | Replace a previously evaluated node-instance with its expanded version
-- @f = g<<const 2>>   -->  node f(...) instantiated `g`@
expandNodeInstDecl :: Env -> NodeInstDecl -> Env
expandNodeInstDecl env nid =
  case nodeInstStaticInputs nid of
    [] ->
      case nodeInstDef nid of
        NodeInst (CallUser f) ps@(_ : _) ->
          case Map.lookup (nameOrigName f) (nodeTemplates env) of
            Just nt ->
              case nt of

                DeclareNode nd ->
                  let prof     = nodeProfile nd
                      (cs,is') = inputBindersToParams (nodeInputs prof)
                      prof'    = prof { nodeInputs = is' }
                  in evalNode env nd { nodeName = nodeInstName nid
                                     , nodeProfile = prof'
                                     , nodeStaticInputs =
                                          nodeStaticInputs nd ++ cs
                                     } ps

                DeclareNodeInst nd ->
                  evalNodeInst env nd { nodeInstName = nodeInstName nid } ps

                _ -> panic "expandNodeInstDecl"
                       [ "Non-node template:"
                       , "*** template: " ++ showPP nt
                       ]

            _ -> panic "expandNodeInstDecl" $
                    [ "Unknown template:"
                    , "*** Name: " ++ showPP f
                    , "*** Available: "
                    ] ++ [ "      " ++ showPP x
                                       | x <- Map.keys (nodeTemplates env) ]

        _ -> doAddNodeInstDecl nid env

    _ -> panic "expandNodeInstDecl"
                [ "Trying to expand a template!"
                , "*** Name: " ++ showPP (nodeInstName nid)
                ]



-- expandIterAt :: Env -> [Binder] -> Iter -> [StaticArg] ->
{-
expandIterAt env resTys it args = undefined
  case (it,args) of
    (IterFill, [ NodeArg _ _ni, sz ], [s]) -> undefined
        {- let s1, x1, y1 = ni s
               s2, x2, y2 = ni s1
               s3, x3, y3 = ni s2
               ...
               sN, xN, yN = ni s{N-1}
           in (sN, [ x1 .. xN ], [ y1 .. yN ]) -}

    (IterRed, [ NodeArg _ ni, sz ], (s : xs)) -> undefined
      {- let s1 = ni (s , x1, y1)
             s2 = ni (s1, x2, y2)
             ...
             sN = ni (s{N-1}, xN, Yn)
         in sN -}

    (IterFill, [ NodeArg _ ni, sz ], (s : xs)) -> undefined
      {- let s1, a1, b1 = ni (s, x1, y1)
             s2, a2, b2 = ni (s1, x2, y2)
             ...
             sN, aN, bN = ni (s{N-1}, xN, yN)
         in (sN, [ a1 .. aN ], [b1 .. bN]) -}


    (IterMap, [ NodeArg _ ni, sz ], xs) -> undefined
      {- let a1, b1 = ni (x1,y1)
             a2, b2 = ni (x2,y2)
             ...
             aN, bN = ni (xN,yN)
          in ([a1..N], [b1..bN]) -}

    (IterBoolRed, [ i, j, n ], [xs]) -> undefined
      {- let n1 = if x1 then 1 else 0
             n2 = if x2 then n1 + 1 else n1 
             ...
             nN = if xN then n{N-1} + 1 else n{N-1}
          in i <= nN && nN <= j
      -}
-}



-- | Add a finished node instance declaration to the environment.
doAddNodeInstDecl :: NodeInstDecl -> Env -> Env
doAddNodeInstDecl ni env =
  env { readyDecls = DeclareNodeInst ni : readyDecls env
      , nodeInfo = case getNodeInstProfile env (nodeInstDef ni) of
                     Just prof -> Map.insert name prof (nodeInfo env)
                     Nothing   -> nodeInfo env
      }
  where name = identOrigName (nodeInstName ni)


--------------------------------------------------------------------------------
-- Typing of Node Instances
-- XXX: This should have happened in the type checker?

{- | Determine the type of a node instance.
Returns 'Maybe' because in some cases we can't determine the
(e.g. some primitives are polymorphic).  We don't name the call sites
for such primitces. -}
getNodeInstProfile :: Env -> NodeInst -> Maybe NodeProfile
getNodeInstProfile env (NodeInst c as) =
  case c of
    CallUser f ->
      case as of
        [] -> case Map.lookup (nameOrigName f) (nodeInfo env) of
                Just a -> Just a
                Nothing -> panic "getNodeInstProfile"
                            [ "Unknown profile for node:"
                            , "*** Node name: " ++ showPP f
                            ]
        _ -> case lookupNodeTemplateInfo (nameOrigName f) env of
               Just (ps,lrProf) ->
                 let env1 = addStaticParams ps as env
                 in case lrProf of
                      Left prof -> Just (evalNodeProfile env1 prof)
                      Right ni  -> getNodeInstProfile env1 ni
               _ -> panic "getNodeInstProfile"
                      [ "Unknown profile for parameterized node:"
                      , "*** Node name: " ++ showPP f
                      ]


    CallPrim _ p ->
      case p of
        Iter it ->
          case it of
            IterFill    ->
              case as of
                [ NodeArg _ ni, ExprArg n ] ->
                  do prof <- getNodeInstProfile env ni
                     case nodeOutputs prof of
                       b : bs -> Just prof { nodeOutputs = b : map (toArr n) bs}
                       _ -> bad
                _ -> bad

            IterRed ->
              case as of
                [ NodeArg _ ni, ExprArg n ] ->
                  do prof <- getNodeInstProfile env ni
                     case nodeInputs prof of
                       b : bs -> Just prof
                                   { nodeInputs = b : map (toArrI n) bs }
                       _ -> bad
                _ -> bad


            IterFillRed ->
              case as of
                [ NodeArg _ ni, ExprArg n ] ->
                  do prof <- getNodeInstProfile env ni
                     case (nodeInputs prof, nodeOutputs prof) of
                       (i:is,o:os) ->
                          Just NodeProfile
                                 { nodeInputs = i : map (toArrI n) is
                                 , nodeOutputs = o : map (toArr n) os
                                 }

                       _ -> bad
                _ -> bad


            IterMap ->
              case as of
                [ NodeArg _ ni, ExprArg n ] ->
                  do prof <- getNodeInstProfile env ni
                     Just NodeProfile
                            { nodeInputs = map (toArrI n) (nodeInputs prof)
                            , nodeOutputs = map (toArr n) (nodeOutputs prof)
                            }
                _ -> bad


            IterBoolRed ->
              panic "getNodeInstProfile"
                [ "Not yet implemented, IterBoolRed" ]
{-
              case as of
                [ _, _, ExprArg k ] ->
                  let ident x = Ident { identText = x
                                      , identRange = range c
                                      , identPragmas = []
                                      , identResolved = undefined
                                      }
                      paramI x t = InputBinder (param x t)
                      param x t = Binder { binderDefines = ident x
                                         , binderType = t
                                         , binderClock = Nothing
                                         }
                  in Just NodeProfile
                            { nodeInputs = [ paramI "a" (ArrayType BoolType k) ]
                            , nodeOutputs = [ param "b" BoolType ]
                            }
                _ -> bad
-}

            where
            toArr n x  = x { binderType = ArrayType (binderType x) n }
            toArrI n x =
              case x of
                InputBinder b ->
                  InputBinder b { binderType = ArrayType (binderType b) n }
                InputConst i t -> InputConst i (ArrayType t n)

            bad = panic "getNodeInstProfile"
                    [ "Unexpecetd iterator instantiation."
                    , "*** Iterator: " ++ showPP it
                    , "*** Arguments: " ++ show ( hsep $ punctuate comma
                                                        $ map pp as )
                    ]
        Op1 _ -> Nothing
        Op2 _ -> Nothing
        OpN _ -> Nothing
        ITE   -> Nothing


--------------------------------------------------------------------------------
-- Static Arguments

addStaticParams :: [ StaticParam ] -> [ StaticArg ] -> Env -> Env
addStaticParams ps as env =
  case (ps,as) of
    ([], []) -> env
    (p : ps1, a : as1) -> addStaticParams ps1 as1 (addStaticParam p a env)
    _ -> panic "addStaticParams" [ "Mismatch in static aruments" ]


addStaticParam :: StaticParam -> StaticArg -> Env -> Env
addStaticParam p a env
  | ArgRange _ a1 <- a = addStaticParam p a1 env  -- XXX: use location?
  | otherwise =
    case p of

      TypeParam i ->
        case a of
          TypeArg t ->
            env { typeAliases = Map.insert (identOrigName i) t
                                                            (typeAliases env) }
          _ -> panic "addStaticParam"
                 [ "Invalid static parameter:"
                 , "*** Expected: a type for " ++ showPP i
                 , "*** Got: " ++ showPP a
                 ]


      ConstParam i t ->
        case a of
          ExprArg e ->
            let cenv   = cEnv env
                val    = evalExprToVal env e
            in env { cEnv = cenv { C.envConsts = Map.insert
                                                  (identOrigName i) val
                                                  (C.envConsts cenv) } }
          _ -> panic "addStaticParam"
                 [ "Invalid static parameter:"
                 , "*** Expected: a constant for " ++
                                      showPP i ++ " : " ++ showPP t
                 , "*** Got: " ++ showPP a
                 ]


      NodeParam _ _ f prof ->
        case a of
          NodeArg _ ni ->
            let nm = identOrigName f
            in env { nodeArgs = Map.insert nm ni   (nodeArgs env)
                   , nodeInfo = Map.insert nm prof (nodeInfo env) }

          _ -> panic "addStaticParam"
                 [ "Invalid static parameter:"
                 , "*** Expected: a node for " ++ showPP f
                 , "*** Got: " ++ showPP a
                 ]






--------------------------------------------------------------------------------
-- Evaluation of expressions


-- | Keep track if we are at the top or nested, to determine
-- when we should name call sites.
data ExprLoc = TopExpr [LHS Expression] | NestedExpr

-- | Rewrite an expression that is not neccessarily constant.
evalDynExpr :: ExprLoc -> Env -> Expression -> M Expression
evalDynExpr eloc env expr =
  case expr of
    ERange r e -> ERange r <$> evalDynExpr eloc (inRange r env) e

    Const e t -> pure (Const (evalExpr env e) (evalCType env t))

    Var {} -> pure expr

    Lit _ -> panic "evalDynExpr" [ "Unexpected `Lit` outside `Const`" ]


    e1 `When` e2    -> do e1' <- evalDynExpr NestedExpr env e1
                          pure (e1' `When` evalClockExpr env e2)

    Tuple es -> Tuple <$> mapM (evalDynExpr NestedExpr env) es
    Array es -> Array <$> mapM (evalDynExpr NestedExpr env) es
    Select e s      -> do e' <- evalDynExpr NestedExpr env e
                          pure (Select e' (evalSel env s))


    -- INVARIANT: the fields in a struct value are in the same order is
    -- in the declaration.
    Struct s fs  -> evalNewStruct env s fs

    -- INVARIANT: the fields in a struct value are in the same order is
    -- in the declaration.
    UpdateStruct ~(Just s) e fs -> evalUpdExprStruct env s e fs

    WithThenElse e1 e2 e3 ->
      case evalExprToVal env e1 of
        VBool b -> if b then evalDynExpr eloc env e2
                        else evalDynExpr eloc env e3
        v       -> panic "evalDynExpr"
                      [ "Decision in `with-then-else` is not a `bool`"
                      , "*** Value: " ++ showPP (valToExpr v)
                      ]

    Merge i ms ->
      case Map.lookup (identOrigName i) (C.envConsts (cEnv env)) of
        Just v  -> evalMergeConst env v ms
        Nothing -> Merge i <$> mapM (evalMergeCase env) ms

    Call f es cl0 ->
      do let cl = evalClockExpr env <$> cl0
         (cs,es0) <-
            case f of
              NodeInst (CallUser c) _ ->
                let nm = nameOrigName c
                in case Map.lookup nm (nodeInfo env) of
                     Just p  -> pure (inputBindersToArgs (nodeInputs p) es)
                     Nothing -> panic "evalDynExpr"
                                  [ "Missing node profile for function."
                                  , "*** Function: " ++ showPP c
                                  ]
              _ -> pure ([],es)
         es' <- do  args <- mapM (evalDynExpr NestedExpr env) es0
                    pure $ case args of
                                 [ e ] | Just xs <- isTuple e -> xs
                                 _ -> args
         ni  <- case (f,cs) of
                  (NodeInst c [],[]) ->
                    pure $
                    case c of
                      CallUser i
                        | Just ni <- Map.lookup (nameOrigName i) (nodeArgs env)
                            -> ni

                      _ -> NodeInst c []
                  (NodeInst c as, _) ->
                        nameInstance env (NodeInst c (as ++ cs))

         shouldName <- case eloc of
                         TopExpr ls ->
                            do case f of
                                 NodeInst (CallUser _) _ ->
                                   recordCallSite (range f) ls
                                 _ -> pure ()
                               pure False
                         NestedExpr -> pure (nameCallSites env)
         if shouldName
            then nameCallSite env ni es' cl
            else pure (Call ni es' cl)

  where
  isTuple e =
    case e of
      ERange _ e1 -> isTuple e1
      Tuple es    -> Just es
      _           -> Nothing



-- | Identify which of the inputs are really static constant parameters.
inputBindersToParams :: [InputBinder] -> ([StaticParam],[InputBinder])
inputBindersToParams = partitionEithers . map classify
  where
  classify ib = case ib of
                  InputBinder _  -> Right ib
                  InputConst i t -> Left (ConstParam i t)

inputBindersToArgs ::
  [InputBinder] -> [Expression] -> ([StaticArg],[Expression])
inputBindersToArgs ins es =
  case (ins,es) of
    ([],[]) -> ([],[])
    (i:is,e:rest) ->
       let (cs,vs) = inputBindersToArgs is rest
       in case i of
            InputBinder _ -> (cs,e:vs)
            InputConst {} -> (ExprArg e : cs,vs)
    _ -> panic "inputBindersToArgs" [ "Type argument mismatch in call."]




-- | Name a call site, by adding an additional equation for the call,
-- and replacing the call with a tuple containing the results.
-- We leave primitives with a single result as calls though.
nameCallSite ::
  Env -> NodeInst -> [Expression] -> Maybe ClockExpr -> M Expression
nameCallSite env ni es cl =
  do mb <- findInstProf env ni
     case mb of
       Just prof ->
         do let ins  = map inB (nodeInputs prof)
                outs = nodeOutputs prof

            let baseName = Text.pack (show (pp ni))
                oName o = case outs of
                            [_] -> baseName
                            _ -> Text.concat
                                  [ baseName, "_", identText (binderDefines o) ]
            let newId o = do i <- newIdent (range ni) Nothing (oName o) AVal
                             pure (origNameToIdent i)
            ns <- mapM newId outs
            let names = map binderDefines (ins ++ outs)
            let nameMap = Map.fromList
                        $ zip names (map isIdent es ++ map Just ns)

                renClock (WhenClock r e i) =  -- loc?
                  WhenClock r (evalExpr env e) $
                    case Map.lookup i nameMap of
                      Just (Just j) -> j
                      Just Nothing ->
                        panic "nameCallSite"
                          [ "Output's clock depends on an input." -- ?
                          , "The clock parameter must be an identifier."
                          , "*** Clock: " ++ showPP i
                          ]
                      _ -> panic "nameCallSite"
                            [ "Undefined clock variable."
                            , "*** Clock: " ++ showPP i ]

                toBind n b = Binder
                               { binderDefines = n
                               , binderType    = binderType b
                               , binderClock =
                                  case binderClock b of
                                    Nothing -> cl
                                    Just curCl -> Just (renClock curCl)
                               }
                binds = zipWith toBind ns outs
            let lhs = map LVar ns
            recordCallSite (range ni) lhs
            addFunEqn binds (Define lhs (Call ni es cl))
            pure $ case map (Var . Unqual) ns of
                     [one] -> one
                     notOne -> Tuple notOne
       Nothing -> pure (Call ni es cl)
  where
  isIdent expr =
     case expr of
       ERange _ e     -> isIdent e
       Var (Unqual i) -> Just i
       _              -> Nothing

  inB inb =
    case inb of
      InputBinder b -> b
      InputConst i t -> panic "nameCallSite"
          [ "Unexpecetd constant parameter"
          , "*** Name: " ++ showPP i
          , "*** Type: " ++ showPP t ]



-- | Use a constant to select a branch in a merge.
evalMergeConst :: Env -> Value -> [MergeCase Expression] -> M Expression
evalMergeConst env v ms =
  case ms of
    MergeCase p e : more
      | evalExprToVal env p == v -> evalDynExpr NestedExpr env e
      | otherwise                -> evalMergeConst env v more
    [] -> panic "evalMergeConst" [ "None of the branches of a merge matched:"
                                 , "*** Value: " ++ showPP (valToExpr v)
                                 ]

-- | Evaluate a case branch of a merge construct.
evalMergeCase :: Env -> MergeCase Expression -> M (MergeCase Expression)
evalMergeCase env (MergeCase p e) =
  MergeCase (evalExpr env p) <$> evalDynExpr NestedExpr env e

-- | Evaluate an update to a struct that is not a constant.
evalUpdExprStruct ::
  Env -> Name -> Expression -> [Field Expression] -> M Expression
evalUpdExprStruct env s e fs =
  do e1  <- evalDynExpr NestedExpr env e
     fs' <- mapM evalField fs
     pure (UpdateStruct (Just s) e1 fs')
  where
  evalField (Field l e1) = Field l <$> evalDynExpr NestedExpr env e1


-- | Evaluate a dynamic expression declaring a struct literal.
-- Missing fields are added by using the default values declared in the type.
evalNewStruct :: Env -> Name -> [Field Expression] -> M Expression
evalNewStruct env s fs =
  evalNewStructWithDefs env s fs $
  case Map.lookup (nameOrigName s) (C.envStructs (cEnv env)) of
    Just def  -> def
    Nothing   -> panic "evalNewStruct" [ "Undefined struct type:"
                                     , "*** Name: " ++ showPP s
                                     ]


{- | Evaluate a dynamic expression declaring a struct literal, using
the given list of fields.  The list if fields should contain all fields
in the struct, and the 'Maybe' value is an optional default--if it is
'Nothing', then the filed must be defined, otherwise the default is used
in case the filed ismissing. -}
evalNewStructWithDefs ::
  Env -> Name -> [Field Expression] -> [(Ident, Maybe Value)] -> M Expression
evalNewStructWithDefs env s fs def =
  do fld <- Map.fromList <$> mapM evalField fs
     pure (Struct s (map (setField fld) def))
  where
  evalField (Field l e) =
    do e1 <- evalDynExpr NestedExpr env e
       return (l,e1)

  setField fld (f,mbV) =
    Field f $
    case Map.lookup f fld of
      Just e -> e
      Nothing ->
        case mbV of
          Just v   -> valToExpr v
          Nothing  -> panic "evalNewStructWithDefs"
                            [ "Missing field in struct:"
                            , "*** Name: " ++ showPP f
                            ]




-- | Generate a new top-level declaration for this node instance.
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




--------------------------------------------------------------------------------
-- Expression Evalutaion Monad

type M = WithBase Id [ ReaderT RO
                     , StateT RW
                     ]

runNameStatic ::
  NameSeed      {- ^ Start generating names using this seed -} ->
  Maybe ModName {- ^ What module are we working on at the moment.
                     'Nothing' means use "global" module -} ->
  M a           {- ^ This is what we want to do -} ->
  (a, [Binder], [ NodeInstDecl ], Map CallSiteId [LHS Expression], NameSeed)
  -- ^ result, new locals, new instances, call site info, new name seed
runNameStatic seed cm m
  | not (isValidNameSeed seed) =
      panic "runNameStatic"
        [ "Incorrect use of `envNameInstSeed`"
        , "*** Negative seed: " ++ show seed
        ]
  | otherwise  = (a, newLocals rw1, reverse (instances rw1)
                 , csInfo rw1
                 , nameSeed rw1)
  where
  (a,rw1) = runId (runStateT rw (runReaderT cm m))
  rw      = RW { nameSeed = seed, instances = [], funEqns = [], newLocals = []
               , csInfo = Map.empty }

type RO = Maybe ModName

data RW = RW
  { nameSeed    :: !NameSeed          -- ^ Generate new names
  , instances   :: [ NodeInstDecl ]   -- ^ Generated declarations
  , newLocals   :: [ Binder ]         -- ^ New locals to declare for 'funEqns'
  , funEqns     :: [ Equation ]       -- ^ Generated named function call sites
  , csInfo      :: Map CallSiteId [LHS Expression]
    -- ^ Identified call sites
  }

recordCallSite :: SourceRange -> [LHS Expression] -> M ()
recordCallSite r xs =
  sets_ $ \s -> s { csInfo = Map.insert (idFromRange r) xs (csInfo s) }


{- | Name the given instantiation.
XXX: For the moment, all new nodes are "safe nodes".
Eventually, we should probably be more accurate and keep track of the
safety & functionality of declarations.
-}
addNameInstDecl :: Callable -> [StaticArg] -> M Name
addNameInstDecl c as =
  do cm <- ask
     i <- newIdent (range c) cm (Text.pack (show (pp c))) ANode
     addInst NodeInstDecl
                { nodeInstSafety        = Safe
                , nodeInstType          = Node
                , nodeInstName          = origNameToIdent i
                , nodeInstStaticInputs  = []
                , nodeInstProfile       = Nothing
                , nodeInstDef           = NodeInst c as
                }
     pure (origNameToName i)




-- | Generate a fresh name associated with the given source location.
newIdent :: SourceRange -> Maybe ModName -> Text -> Thing -> M OrigName
newIdent r md txt th = sets $ \s ->
  let uid     = nameSeed s
      origI   = Ident { identRange    = r
                      , identText     = txt
                      , identPragmas  = []
                      , identResolved = Nothing
                      }
      origN   = OrigName { rnUID    = nameSeedToInt uid
                         , rnModule = md
                         , rnIdent  = origI
                         , rnThing  = th
                         }

      s1 = s { nameSeed = nextNameSeed uid }
  in s1 `seq` (origN, s1)


-- | Remember the given instance.
addInst :: NodeInstDecl -> M ()
addInst ni = sets_ $ \s -> s { instances = ni : instances s }

findInstProf :: Env -> NodeInst -> M (Maybe NodeProfile)
findInstProf env ni@(NodeInst c as) =
  case (c,as) of
    (CallUser n, [])
       | Unqual i <- n -> search (identText i)
       where
       search t = do is <- instances <$> get
                     case filter ((t ==) . identText . nodeInstName) is of
                       d : _ -> findInstProf env (nodeInstDef d)
                       _ -> pure (getNodeInstProfile env ni)

    _ -> pure (getNodeInstProfile env ni)


-- | Run a computation and collect all named function call sites,
-- returning them.  The result of the computation is added last to the list.
collectFunEqns :: M Equation -> M [Equation]
collectFunEqns m =
  do e <- m
     sets $ \s -> (reverse (e : funEqns s), s { funEqns = [] })

-- | Record a new function equation.
addFunEqn :: [Binder] -> Equation -> M ()
addFunEqn bs eqn = sets_ $ \s -> s { newLocals = bs ++ newLocals s
                                   , funEqns = eqn : funEqns s }
