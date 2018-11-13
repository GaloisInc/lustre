{-# Language OverloadedStrings #-}

{- | This module inlines all functions at their call sites.
Assumptions:
  * Functions have been named, so they only appear at the top-level
    if equations.(see nameCallSites in NoStatic)
  * Top-level instance have been expaned (see expandNodeInsts in NoStatic)
  * Equations contan only simple (i.e., 'LVar') 'LHS's.
  * No constants
-}
module Language.Lustre.Transform.Inline (quickInlineCalls) where

import Data.Text(Text)
import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List(mapAccumL)
import Data.Semigroup ( (<>) )

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic
import Language.Lustre.Utils


quickInlineCalls :: [TopDecl] -> (AllRenamings,[TopDecl])
quickInlineCalls = inlineCalls emptyEnv

data Env = Env
  { envNodes      :: Map Name NodeDecl
    -- ^ Definitions for nodes that are in scope.

  , envCurModule  :: Maybe Text
    -- ^ Use this qualifier for the current module
  }

emptyEnv :: Env
emptyEnv = Env { envNodes = Map.empty, envCurModule = Nothing }

{- The plan:

Given:

node f (a : A; b : B) returns (c : C; d : D)
  var e : E;
let
  e = e3
  c = e4
  d = e5
  assume e6
  show e7
tel


And a use site within some node `g`:

node g (...) returns (..)
  var ...

let
  ...
  x,y = f (e1,e2)
  ...
tel

Transform `g` as follows:

1. Compute name renaming:
  a -> a1   -- choose non-clashing names
  b -> b1   -- ditto
  e -> e1   -- choose non-clashing name for
  c -> x    -- match output with LHS
  d -> y    -- ditto


2. New definition of `g`:

node g(...) returns (...)
  var ...
  var a1 : A;   -- non-clashing names for params
  var b1 : B;   -- non-clashing names for params
  var e1 : E;   -- non-clashing names for locals
let
  ...
  a1 = e1       -- renamed params
  a2 = e2       -- ditto
  e1 = e3 [renaming]
  x  = e4 [renaming]
  y  = e5 [renaming]
  show (e6 [renaming])  -- prove that concrete values match expectations
  args_ok = e6[renaming] and ... others ...
  show (args_ok => e7 [renaming])
    -- note: no polarity switching, but we assume that inputs were OK
  ...

-}

-- | An "infinite" list of variations on a name
nameVariants :: Ident -> [Ident]
nameVariants i = i : [ i { identText = variant n } | n <- [ 1 :: Integer .. ] ]
  where
  base = identText i
  variant n = base <> "_" <> Text.pack (show n)


-- | A set of used up names.  When we generate new names, we look for names
-- that are not in this set.
type UsedNames = Set Ident

-- | Pick a variant of the given name that does not clash with anything in the
-- environment.  Also add the new name to the set of names to be avoided.
freshName :: UsedNames -> Ident -> (UsedNames, Ident)
freshName used i = (newUsed, name)
  where
  name : _  = [ j | j <- nameVariants i, not (j `Set.member` used) ]
  newUsed   = Set.insert name used


-- | Change the name of a binder to avoid name clasehs.
freshBinder :: UsedNames -> Binder -> (UsedNames, Binder)
freshBinder used b = (newUsed, newBinder)
  where
  (newUsed, newName)  = freshName used (binderDefines b)
  newBinder           = b { binderDefines = newName }


-- | A mapping from old names, to their clash-avoiding versions.
type Renaming = Map Ident Ident


-- | Compute the renaming to be used when instantiating the given node.
computeRenaming ::
  UsedNames             {- ^ Dont't use these names -} ->
  [LHS Expression]      {- ^ LHS of call site -} ->
  NodeDecl              {- ^ Function being called -} ->
  (UsedNames, Renaming, [LocalDecl], [Ident])
  -- ^ new used, renaming of identifiers, new locals to add
  -- Last argument is a "call site id",  which is used for showing traces
  -- (i.e., a kind of inverse)
computeRenaming used lhs nd =
  (newUsed, renaming, map LocalVar newBidners, map lhsIdent lhs)
  where
  prof = nodeProfile nd
  def  = case nodeDef nd of
           Just b -> b
           Nothing -> panic "computeRenaming"
                        [ "The node has no definition."
                        , "*** Node: " ++ showPP nd ]

  lhsIdent l = case l of
                 LVar i -> i
                 _      -> panic "computeRenaming"
                              [ "LHS is not a simple identifier."
                              , "*** LHS: " ++ showPP l ]


  oldBinders            = map inputBinder (nodeInputs prof) ++
                          map localBinder (nodeLocals def)
  (newUsed,newBidners)  = mapAccumL freshBinder used oldBinders


  renOut b l            = (binderDefines b,   lhsIdent l)
  renBind old new       = (binderDefines old, binderDefines new)

  renaming              = Map.fromList $
                            zipExact renOut (nodeOutputs prof) lhs ++
                            zipExact renBind oldBinders newBidners

inputBinder :: InputBinder -> Binder
inputBinder ib =
  case ib of
    InputBinder b -> b
    InputConst i t -> panic "inputBinder"
                        [ "Unexpected constant parameter."
                        , "Constants should have been eliminated by now."
                        , "*** Name: " ++ showPP i
                        , "*** Type: " ++ showPP t ]

localBinder :: LocalDecl -> Binder
localBinder l = case l of
                 LocalVar b -> b
                 LocalConst cd ->
                   panic "computeRenaming"
                     [ "Unexpected local constant."
                     , "Constants should have been eliminated by now."
                     , "*** Constant: " ++ showPP cd
                     ]



--------------------------------------------------------------------------------
-- Applying a renaming

-- | We dont visit constant expressions.
-- There shouldn't be any, and the renaming CURRENTLY should
-- contain any constants
class Rename t where
  rename :: Renaming -> t -> t

instance Rename a => Rename [a] where
  rename su xs = rename su <$> xs

instance Rename a => Rename (Maybe a) where
  rename su xs = rename su <$> xs

instance Rename Ident where
  rename su i = Map.findWithDefault i i su

instance Rename Name where
  rename su x = case x of
                  Unqual i -> Unqual (rename su i)
                  _        -> x

instance Rename Expression where
  rename su expr =
    case expr of
      ERange r e -> ERange r (rename su e)
      Var x      -> Var (rename su x)
      Lit _      -> expr

      e `When` ce -> rename su e `When` rename su ce

      -- These are probably eliminated, but we define them as they make sense
      Tuple es        -> Tuple (rename su es)
      Array es        -> Array (rename su es)
      Select e s      -> Select (rename su e) s
      Struct x mb fs  -> Struct x (rename su mb) (rename su fs)
      WithThenElse e1 e2 e3 ->
        WithThenElse e1 (rename su e2)  (rename su e3)

      Merge i ms -> Merge (rename su i) (rename su ms)
      CallPos ni es -> CallPos ni (rename su es)

instance Rename e => Rename (Field e) where
  rename su (Field l e) = Field l (rename su e)

instance Rename ClockExpr where
  rename su (WhenClock r e i) = WhenClock r e (rename su i)

instance Rename e => Rename (MergeCase e) where
  rename su (MergeCase a b) = MergeCase a (rename su b)

instance Rename a => Rename (LHS a) where
  rename su lhs =
    case lhs of
      LVar b      -> LVar (rename su b)
      LSelect l s -> LSelect (rename su l) s

instance Rename Equation where
  rename su eqn =
    case eqn of
      Assert x e    -> Assert x (rename su e)    -- XXX: change names?
      Property x e  -> Property x (rename su e)  -- XXX: change names?
      IsMain r      -> IsMain r
      Define ls e   -> Define (rename su ls) (rename su e)
      IVC is        -> IVC (rename su is)

--------------------------------------------------------------------------------

-- | Inline the "normal" calls in a node declaration.
-- We assume that the calls in the definition have been already inlined,
-- so we don't continue inlining recursively.
inlineCallsNode :: Env -> NodeDecl -> (Map [Ident] (Name,Renaming), NodeDecl)
inlineCallsNode env nd =
  case nodeDef nd of
    Nothing -> (Map.empty,nd)
    Just def
      | null (nodeStaticInputs nd) ->
        let prof = nodeProfile nd
            used = Set.fromList $ map binderDefines $
                      map inputBinder (nodeInputs prof) ++
                      nodeOutputs prof ++
                      map localBinder (nodeLocals def)
            (newLocs,newEqs,rens) = renameEqns used (nodeEqns def)
        in ( rens
           , nd { nodeDef = Just NodeBody
                                  { nodeLocals = newLocs ++ nodeLocals def
                                  , nodeEqns   = newEqs
                                  } }
           )

      | otherwise ->
        panic "inlineCalls" [ "Unexpected static arguments."
                            , "*** Node: " ++ showPP nd ]

  where
  isCall e =
    case e of
      ERange _ e1   -> isCall e1
      CallPos (NodeInst (CallUser f) []) es -> Just (f,es)
      _             -> Nothing

  renameEqns used eqns =
    case eqns of
      [] -> ([],[],Map.empty)
      eqn : more ->
        case eqn of
          Define ls e
            | Just (f,es) <- isCall e
            , Just cnd    <- Map.lookup f (envNodes env)
            , Just def    <- nodeDef cnd ->
            let prof = nodeProfile cnd
                (newUsed, su, newLocals,key) = computeRenaming used ls cnd
                paramDef b p = Define [ LVar (rename su (binderDefines b)) ] p
                paramDefs    = zipExact paramDef
                                        (map inputBinder (nodeInputs prof)) es
                thisEqns     = updateProps (rename su (nodeEqns def))
                (otherDefs,otherEqns,rens) = renameEqns newUsed more
            in ( newLocals ++ otherDefs
               , paramDefs ++ thisEqns ++ otherEqns
               , Map.insert key (f,su) rens
               )

          _ -> let (otherDefs, otherEqns, rens) = renameEqns used more
               in (otherDefs, eqn : otherEqns, rens)

  updateProps eqns =
    let asmps = [ e | Assert _ e <- eqns ]
        bin r f a b = CallPos (NodeInst (CallPrim r (Op2 f)) []) [a,b]

        addAsmps e1 = case asmps of
                        [] -> e1
                        [a] -> bin (range e1) Implies a e1
                        as  -> bin (range e1) Implies
                                   (foldr1 (bin (range e1) And) as)
                                   e1
        upd eqn = case eqn of
                    Assert x e   -> Property x e
                    Property x e -> Property x (addAsmps e)
                    _            -> eqn
    in map upd eqns

inlineCalls :: Env -> [TopDecl] -> (AllRenamings,[TopDecl])
inlineCalls env ds =
  case ds of
    [] -> (Map.empty,[])
    DeclareNode nd : more ->
      let (thisRens,nd1) = inlineCallsNode env nd
          (allRens,nds)  = inlineCalls (addNodeDecl nd1 env) more
      in ( Map.insert (nodeName nd) thisRens allRens
         , DeclareNode nd1 : nds
         )
    d : more -> let (allRens, newDs) = inlineCalls env more
                in (allRens, d : newDs)

addNodeDecl :: NodeDecl -> Env -> Env
addNodeDecl nd env = env { envNodes = Map.insert (Unqual i) nd
                                    $ addQual $ envNodes env }
  where
  i = nodeName nd
  addQual = case envCurModule env of
              Nothing -> id
              Just m  -> Map.insert (Qual (identRange i) m (identText i)) nd

--------------------------------------------------------------------------------
-- Resugar

-- | Maps (node name, call_site as list of ident, name in call, to local name)
type AllRenamings = Map Ident (Map [Ident] (Name,Renaming))


