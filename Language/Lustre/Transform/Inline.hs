{-# Language OverloadedStrings, GeneralizedNewtypeDeriving, DataKinds #-}

{- | This module inlines all functions at their call sites.
Assumptions:
  * Functions have been named, so they only appear at the top-level
    if equations.(see nameCallSites in NoStatic)
  * Top-level instance have been expaned (see expandNodeInsts in NoStatic)
  * Equations contan only simple (i.e., 'LVar') 'LHS's.
  * No constants
-}
module Language.Lustre.Transform.Inline
        (inlineCalls, AllRenamings, Renaming(..)) where

import Data.Map (Map)
import qualified Data.Map as Map
import MonadLib
import Data.Traversable(for)

import Language.Lustre.Name
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
  GLOBAL assume e8
tel


And a use site within some node `g`:

node g (...) returns (..)
  var ...

let
  ...
  x,y = f ((e1,e2) when t)
  ...
tel

Transform `g` as follows:

1. Compute name renaming:
  a -> a1   -- choose non-clashing names inputs
  b -> b1   -- ditto
  e -> e1   -- choose non-clashing name for locals
  c -> x    -- match output with LHS
  d -> y    -- ditto


2. New definition of `g`:

node g(...) returns (...)
  var ...
  var a1 when t : A;   -- non-clashing names for params
  var b1 when t : B;   -- non-clashing names for params
  var e1 when t : E;   -- non-clashing names for locals
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
    -- this ensure that the spec on `f` was OK
  GLOBAL assume e8[renaming]
    -- no plarity switchin on global assumptions, as these are assumptions
    -- about the environment that we just inheirt in our spec.


3. Modular Reasoning

Consider:
   f (x : real) returns (y : real)
   let
      assume e1
      show e2
   tel

Sometimes we may want to construct a proof which *assumes* that `f`
is working correctly.  In that case, we translate `g` a bit different:

node g(...) returns (...)
  var ...
  var a1 when t : A;   -- non-clashing names for params
  var b1 when t : B;   -- non-clashing names for params
let
  ...
  a1 = e1       -- renamed params
  a2 = e2       -- ditto
  -- no definitions for results
  show (e6 [renaming])  -- prove that concrete values match expectations
  args_ok = e6[renaming] and ... others ...
  GLOBAL assume (args_ok => e7 [renaming])

  NOTE: this assumes that guarantees do not mention any local variables.
  if they do, then we'd have to also add the definitions of those variables.
  ...
-}


-- | Change the name of a binder to avoid name clasehs.
freshBinder :: Binder -> InM Binder
freshBinder b = do n <- freshName (binderDefines b)
                   pure b { binderDefines = n }


-- | A mapping from old names to their clash-avoiding versions.
data Renaming = Renaming
  { renVarMap :: Map OrigName OrigName
    -- ^ Mapping of names.

  , renClock  :: IClock
    -- ^ Clock at the call site, if any.
    -- If this is set, then we have to replace base clocks with this clock
    -- in the inlined code.
  }


-- | Compute the renaming to be used when instantiating the given node.
computeRenaming ::
  IClock                {- ^ Clock at the call site -} ->
  [LHS Expression]      {- ^ LHS of call site -} ->
  NodeDecl              {- ^ Function being called -} ->
  InM (Renaming, [LocalDecl], [OrigName])
  -- ^ renaming of identifiers, new locals to add
  -- Last result is a "call site id",  which is used for showing traces
  -- (i.e., a kind of inverse)
computeRenaming cl lhs nd =
  do newBinders <-
       for oldBinders $ \b ->
         do n <- freshBinder b
            pure $ case cl of
                     BaseClock -> n -- still need to apply subst to clocks
                     KnownClock c ->
                       case cClock (binderType n) of
                         BaseClock ->
                           let ct = binderType n
                           in n { binderType = ct { cClock = KnownClock c } }
                         KnownClock _ -> n -- still need to apply su
                         ClockVar i -> panic "computeRenaming"
                                      [ "Unexpected clock variable", showPP i ]

                     ClockVar i -> panic "computeRenaming"
                                      [ "Unexpected clock variable", showPP i ]

     let renaming = Renaming
                      { renVarMap = Map.fromList $
                                    zipExact renOut (nodeOutputs prof) lhs ++
                                    zipExact renBind oldBinders newBinders
                      , renClock = cl
                      }
         renB b = b { binderType = rename renaming (binderType b) }
     pure (renaming, map (LocalVar . renB) newBinders, map lhsIdent lhs)
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
  rename su i = case Map.lookup (identOrigName i) (renVarMap su) of
                  Just n  -> origNameToIdent n
                  Nothing -> i

instance Rename Name where
  rename su x = case Map.lookup (nameOrigName x) (renVarMap su) of
                  Just n  -> origNameToName n
                  Nothing -> x

instance Rename Expression where
  rename su expr =
    case expr of
      ERange r e      -> ERange r (rename su e)
      Const e t       -> Const e (rename su t)
      Var x           -> Var (rename su x)
      Lit _           -> bad "literal, not under Const"

      e `When` ce     -> rename su e `When` rename su ce

      Merge i ms      -> Merge (rename su i) (rename su ms)
      Call ni es c    -> Call ni (rename su es) (rename su c)

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

instance Rename CType where
  rename su ct = ct { cClock = rename su (cClock ct) }

instance Rename IClock where
  rename su clk =
    case clk of
      BaseClock -> renClock su
      KnownClock c -> KnownClock (rename su c)
      ClockVar {}  -> panic "Inline.rename" [ "Unexpected clock variable." ]

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
      Assert x ty e -> Assert x ty (rename su e)    -- XXX: change names?
      Property x e  -> Property x (rename su e)  -- XXX: change names?
      IsMain r      -> IsMain r
      Define ls e   -> Define (rename su ls) (rename su e)
      IVC is        -> IVC (rename su is)
      Realizable is -> Realizable (rename su is)

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
      Call (NodeInst (CallUser f) []) es cl -> Just (f,es,cl)
      _             -> Nothing

  renameEqns ready eqns =
    case eqns of
      [] -> pure ([],[],Map.empty)
      eqn : more ->
        case eqn of
          Define ls e
            | Just (f,es,cl) <- isCall e
            , let fo = nameOrigName f
            , Just cnd <- Map.lookup fo ready
            , Just def <- nodeDef cnd ->
            do let prof = nodeProfile cnd
               (su, newLocals, key) <- computeRenaming cl ls cnd
               let paramDef b p = Define [LVar (rename su (binderDefines b))] p
                   paramDefs    = zipExact paramDef
                                        (map inputBinder (nodeInputs prof)) es
                   thisEqns     = updateProps (nodeExtern cnd)
                                              (rename su (nodeEqns def))
               (otherDefs,otherEqns,rens) <- renameEqns ready more
               pure ( newLocals ++ otherDefs
                    , paramDefs ++ thisEqns ++ otherEqns
                    , Map.insert key (fo,su) rens
                    )

          _ -> do (otherDefs, otherEqns, rens) <- renameEqns ready more
                  pure (otherDefs, eqn : otherEqns, rens)

  updateProps extern eqns =
    let asmps = [ e | Assert _ AssertPre e <- eqns ]

        addAsmps e1 = case asmps of
                        [] -> e1
                        [a] -> eOp2 (range e1) Implies a e1
                        as  -> eOp2 (range e1) Implies
                                   (foldr1 (eOp2 (range e1) And) as)
                                   e1
        upd eqn = case eqn of
                    Assert x ty e ->
                       case ty of
                          AssertPre -> Property x e
                          AssertEnv -> Assert x AssertEnv e

                    Property x e
                      | extern -> Assert x AssertEnv (addAsmps e)
                      | otherwise -> Property x (addAsmps e)
                    _ -> eqn
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

-- | Maps (node name, call_site as list of name, function called, renamed)
-- XXX: Identifying call sites by something other than list of ids.
type AllRenamings = Map OrigName    {-node name-} (
                    Map [OrigName]  {-call site-}
                        ( OrigName  {-called node-}
                        , Renaming  {-how names changed, and we called-}
                        )
                    )

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




