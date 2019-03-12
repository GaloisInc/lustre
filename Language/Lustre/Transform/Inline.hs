{-# Language OverloadedStrings, GeneralizedNewtypeDeriving, DataKinds #-}

{- | This module inlines all functions at their call sites.
Assumptions:
  * Functions have been named, so they only appear at the top-level
    if equations.(see nameCallSites in NoStatic)
  * Top-level instance have been expaned (see expandNodeInsts in NoStatic)
  * Equations contan only simple (i.e., 'LVar') 'LHS's.
  * No constants
-}
module Language.Lustre.Transform.Inline (inlineCalls, AllRenamings) where

import Data.Map (Map)
import qualified Data.Map as Map
import MonadLib

import Language.Lustre.AST
import Language.Lustre.Monad
import Language.Lustre.Pretty
import Language.Lustre.Panic
import Language.Lustre.Utils

-- | Inline the calls from the given top declarations.  Resturns information
-- about how things got renames, as well as new list of declarations.
inlineCalls :: [NodeDecl] {- ^ Already inline decls from environment -} ->
               [TopDecl]  {- ^ More decls to process -} ->
               LustreM (AllRenamings,[TopDecl])
inlineCalls ini ds = runInM ini (mapM inlineDecl ds)


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


-- | Change the name of a binder to avoid name clasehs.
freshBinder :: Binder -> InM Binder
freshBinder b = do n <- freshName (binderDefines b)
                   pure b { binderDefines = n }


-- | A mapping from old names to their clash-avoiding versions.
type Renaming = Map OrigName OrigName


-- | Compute the renaming to be used when instantiating the given node.
computeRenaming ::
  [LHS Expression]      {- ^ LHS of call site -} ->
  NodeDecl              {- ^ Function being called -} ->
  InM (Renaming, [LocalDecl], [OrigName])
  -- ^ new used, renaming of identifiers, new locals to add
  -- Last argument is a "call site id",  which is used for showing traces
  -- (i.e., a kind of inverse)
computeRenaming lhs nd =
  do newBinders <- mapM freshBinder oldBinders
     let renaming = Map.fromList $
                      zipExact renOut (nodeOutputs prof) lhs ++
                      zipExact renBind oldBinders newBinders
     pure (renaming, map LocalVar newBinders, map lhsIdent lhs)
  where
  prof = nodeProfile nd
  def  = case nodeDef nd of
           Just b -> b
           Nothing -> panic "computeRenaming"
                        [ "The node has no definition."
                        , "*** Node: " ++ showPP nd ]


  oldBinders            = map inputBinder (nodeInputs prof) ++
                          map localBinder (nodeLocals def)

  lhsIdent l = case l of
                 LVar i -> identOrigName i
                 _      -> panic "computeRenaming"
                              [ "LHS is not a simple identifier."
                              , "*** LHS: " ++ showPP l ]

  renOut b l            = (identOrigName (binderDefines b),   lhsIdent l)
  renBind old new       = ( identOrigName (binderDefines old)
                          , identOrigName (binderDefines new)
                          )


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
                   panic "localBinder"
                     [ "Unexpected local constant."
                     , "Constants should have been eliminated by now."
                     , "*** Constant: " ++ showPP cd
                     ]



--------------------------------------------------------------------------------
-- Applying a renaming, used when instantiatiating inlined functions.

-- | We don't visit constant expressions, as they should contain no variables
-- by this stage (i.e., they ought to be constant values).
class Rename t where
  rename :: Renaming -> t -> t

instance Rename a => Rename [a] where
  rename su xs = rename su <$> xs

instance Rename a => Rename (Maybe a) where
  rename su xs = rename su <$> xs

instance Rename Ident where
  rename su i = case Map.lookup (identOrigName i) su of
                  Just n  -> origNameToIdent n
                  Nothing -> i

instance Rename Name where
  rename su x = case Map.lookup (nameOrigName x) su of
                  Just n  -> origNameToName n
                  Nothing -> x

instance Rename Expression where
  rename su expr =
    case expr of
      ERange r e      -> ERange r (rename su e)
      Var x           -> Var (rename su x)
      Lit _           -> expr

      e `When` ce     -> rename su e `When` rename su ce
      CondAct {}      -> bad "condact"

      Merge i ms      -> Merge (rename su i) (rename su ms)
      Call ni es      -> Call ni (rename su es)

      Tuple {}        -> bad "tuple"
      Array {}        -> bad "array"
      Select {}       -> bad "select"
      Struct {}       -> bad "struct"
      UpdateStruct {} -> bad "struct update"
      WithThenElse {} -> bad "with-then-else"
    where
    bad x = panic "rename" [ "Unexepected " ++ x ]

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
      LSelect {}  -> panic "rename" [ "Unexepected LHS select" ]

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
inlineCallsNode ::
  NodeDecl -> InM (Map [OrigName] (OrigName,Renaming), NodeDecl)
inlineCallsNode nd =
  case nodeDef nd of
    Nothing -> pure (Map.empty,nd)
    Just def
      | null (nodeStaticInputs nd) ->
        do ready <- doneNodes
           (newLocs,newEqs,rens) <- renameEqns ready (nodeEqns def)
           pure ( rens
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
      Call (NodeInst (CallUser f) []) es -> Just (f,es)
      _             -> Nothing

  renameEqns ready eqns =
    case eqns of
      [] -> pure ([],[],Map.empty)
      eqn : more ->
        case eqn of
          Define ls e
            | Just (f,es) <- isCall e
            , let fo = nameOrigName f
            , Just cnd <- Map.lookup fo ready
            , Just def <- nodeDef cnd ->
            do let prof = nodeProfile cnd
               (su, newLocals, key) <- computeRenaming ls cnd
               let paramDef b p = Define [LVar (rename su (binderDefines b))] p
                   paramDefs    = zipExact paramDef
                                        (map inputBinder (nodeInputs prof)) es
                   thisEqns     = updateProps (rename su (nodeEqns def))
               (otherDefs,otherEqns,rens) <- renameEqns ready more
               pure ( newLocals ++ otherDefs
                    , paramDefs ++ thisEqns ++ otherEqns
                    , Map.insert key (fo,su) rens
                    )

          _ -> do (otherDefs, otherEqns, rens) <- renameEqns ready more
                  pure (otherDefs, eqn : otherEqns, rens)

  updateProps eqns =
    let asmps = [ e | Assert _ e <- eqns ]
        bin r f a b = Call (NodeInst (CallPrim r (Op2 f)) []) [a,b]

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

inlineDecl :: TopDecl -> InM TopDecl
inlineDecl d =
  case d of
    DeclareNode nd ->
      do (thisRens,nd1) <- inlineCallsNode nd
         addNodeDecl thisRens nd1
         pure (DeclareNode nd1)
    _ -> pure d

--------------------------------------------------------------------------------
-- Resugar

-- | Maps (node name, call_site as list of ident, function called, renamed)
type AllRenamings = Map OrigName (Map [OrigName] (OrigName,Renaming))

--------------------------------------------------------------------------------

newtype InM a = InM { unInM :: StateT RW LustreM a }
  deriving (Functor,Applicative,Monad)

data RW = RW
  { inlinedNodes :: !(Map OrigName NodeDecl)
    -- ^ Nodes that have been processed already.

  , renamings    :: AllRenamings
    -- ^ How we renamed things, for propagating answers back.
  }

runInM :: [NodeDecl] -> InM a -> LustreM (AllRenamings, a)
runInM ini m =
  do (a,s1) <- runStateT s $ unInM m
     pure (renamings s1, a)
  where
  s         = RW { inlinedNodes = Map.fromList (map entry ini)
                 , renamings    = Map.empty
                 }
  entry nd  = (identOrigName (nodeName nd), nd)

-- | Add an inlined node to the collection of processed nodes.
addNodeDecl ::
  Map [OrigName] (OrigName,Renaming) {- ^ Info about inlined vars -} ->
  NodeDecl {- ^ Inlined function -} ->
  InM ()
addNodeDecl rens nd = InM $
  sets_ $ \s -> s { inlinedNodes = Map.insert i nd (inlinedNodes s)
                  , renamings = Map.insert i rens (renamings s)  }
  where i = identOrigName (nodeName nd)

doneNodes :: InM (Map OrigName NodeDecl)
doneNodes = InM $ inlinedNodes <$> get

{- | Generate a new version of the given identifier. -}
freshName :: Ident -> InM Ident
freshName i =
  do u <- InM (inBase newInt)
     let newON = (identOrigName i) { rnUID = u }
     pure i { identResolved = Just newON }




