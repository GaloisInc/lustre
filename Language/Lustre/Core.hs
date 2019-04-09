{-# Language OverloadedStrings #-}
module Language.Lustre.Core
  (module Language.Lustre.Core, Literal(..)) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import Text.PrettyPrint( Doc, text, (<+>)
                       , hsep, nest, parens, punctuate, comma, ($$) )
import qualified Text.PrettyPrint as PP

import Language.Lustre.AST (Literal(..),PropName(..))
import Language.Lustre.Name
import Language.Lustre.Pretty
import Language.Lustre.Panic(panic)


-- XXX: Support for integer ranges.
-- This would be useful to model enums, as well as "subrange [x,y] of int"
data Type     = TInt | TReal | TBool
                deriving Show

-- | A boolean clock.  The base clock is always @true@.
data Clock    = BaseClock | WhenTrue Atom
                deriving Show

-- | Type on a boolean clock.
data CType    = Type `On` Clock
                deriving Show

typeOfCType :: CType -> Type
typeOfCType (t `On` _) = t

clockOfCType :: CType -> Clock
clockOfCType (_ `On` c) = c

data Binder   = Ident ::: CType
                deriving Show

data Atom     = Lit Literal CType
              | Var Ident
              | Prim Op [Atom]
                deriving Show

data Expr     = Atom Atom
              | Atom :-> Atom
              | Pre Atom
              | Atom `When` Atom
              | Current Atom
              | Merge Atom Atom Atom
                deriving Show

data Op       = Not | Neg
              | IntCast | RealCast | FloorCast
              | And | Or | Xor | Implies
              | Eq | Neq | Lt | Leq | Gt | Geq
              | Mul | Mod | Div | Add | Sub | Power
              | ITE
              | AtMostOne | Nor
                deriving Show

data Eqn      = Binder := Expr
                deriving Show

infix 1 :=
infix 2 :::
infix 3 `On`

data Node     = Node { nInputs      :: [Binder]
                     , nOutputs     :: [Ident]

                     , nAssuming    :: [(PropName,Ident)]
                       -- ^ Assuming that these are true

                     , nShows       :: [(PropName,Ident)]
                       -- ^ Need to show that these are also true

                     , nEqns        :: [EqnGroup]
                       -- ^ Groups of recursive equations.
                     } deriving Show

-- | One or more equations.
data EqnGroup = NonRec Eqn    -- ^ A non-recursive equation
              | Rec [Eqn]     -- ^ A group of recursive equations.
                deriving Show

grpEqns :: EqnGroup -> [Eqn]
grpEqns g =
  case g of
    NonRec e -> [e]
    Rec es   -> es


--------------------------------------------------------------------------------
-- Ordering equations

usesAtom :: Atom -> Set Ident
usesAtom atom =
  case atom of
    Lit _ _   -> Set.empty
    Var x     -> Set.singleton x
    Prim _ as -> Set.unions (map usesAtom as)

usesExpr :: Expr -> Set Ident
usesExpr expr =
  case expr of
    Atom a        -> usesAtom a
    a1 :-> a2     -> Set.union (usesAtom a1) (usesAtom a2)
    Pre _         -> Set.empty -- refer to values at previous instance
    a1 `When` a2  -> Set.union (usesAtom a1) (usesAtom a2)
    Current a     -> usesAtom a
    Merge a b c   -> Set.unions (map usesAtom [a,b,c])

usesClock :: Clock -> Set Ident
usesClock c =
  case c of
    BaseClock -> Set.empty
    WhenTrue a -> usesAtom a

-- | Order the equations.  Returns cycles on the left, if there are some.
orderedEqns :: [Eqn] -> [EqnGroup]
orderedEqns eqns = map cvt (stronglyConnComp graph)
  where
  graph = [ (eqn, x, Set.toList (Set.union (usesClock c) (usesExpr e)))
              | eqn <- eqns, let (x ::: _ `On` c) := e = eqn ]
  cvt x = case x of
            AcyclicSCC e -> NonRec e
            CyclicSCC es -> Rec es


--------------------------------------------------------------------------------
-- Pretty Printing


-- | Local identifier numbering. See `identVariants`.
type PPInfo = Map Ident Int

noInfo :: PPInfo
noInfo = Map.empty

ppPrim :: Op -> Doc
ppPrim = text . show

ppIdent :: PPInfo -> Ident -> Doc
ppIdent info i =
  case Map.lookup i info of
    Nothing -> pp (identText i) PP.<> "$u" PP.<> PP.int (identUID i)
    Just 0  -> pp i
    Just n  -> pp i PP.<> "$" PP.<> PP.int n

ppType :: Type -> Doc
ppType ty =
  case ty of
    TInt  -> text "int"
    TReal -> text "real"
    TBool -> text "bool"

ppCType :: PPInfo -> CType -> Doc
ppCType env (t `On` c) =
  case c of
    BaseClock  -> ppType t
    WhenTrue a -> ppType t <+> "when" <+> ppAtom env a

ppBinder :: PPInfo -> Binder -> Doc
ppBinder env (x ::: t) = ppIdent env x <+> text ":" <+> ppCType env t

ppAtom :: PPInfo -> Atom -> Doc
ppAtom env atom =
  case atom of
    Lit l c   -> case clockOfCType c of
                   BaseClock  -> pp l
                   WhenTrue a -> pp l <+> "/* when" <+> ppAtom env a <+> "*/"
    Var x     -> ppIdent env x
    Prim f as -> ppPrim f PP.<> ppTuple (map (ppAtom env) as)

ppExpr :: PPInfo -> Expr -> Doc
ppExpr env expr =
  case expr of
    Atom a      -> ppAtom env a
    a :-> b     -> ppAtom env a <+> text "->" <+> ppAtom env b
    Pre a       -> text "pre" <+> ppAtom env a
    a `When` b  -> ppAtom env a <+> text "when" <+> ppAtom env b
    Current a   -> text "current" <+> ppAtom env a
    Merge a b c ->
      text "merge" <+> ppAtom env a <+> ppAtom env b <+> ppAtom env c


ppTuple :: [Doc] -> Doc
ppTuple ds = parens (hsep (punctuate comma ds))

ppEqn :: PPInfo -> Eqn -> Doc
ppEqn env (b := e) =
  ppBinder env b $$ nest 2 ("=" <+> ppExpr env e)

ppEqnGroup :: PPInfo -> EqnGroup -> Doc
ppEqnGroup env grp =
  case grp of
    NonRec eqn -> ppEqn env eqn
    Rec eqns   -> "rec" $$ nest 2 (vcatSep (map (ppEqn env) eqns))


ppNode :: Node -> Doc
ppNode node =
  text "node" <+> ppTuple (map (ppBinder env) (nInputs node))
  $$ nest 2 (  text "returns" <+> ppTuple (map (ppIdent env) (nOutputs node))
            $$ text "assumes" <+> ppTuple (map (ppIdent env . snd)
                                                (nAssuming node))
            $$ text "shows" <+> ppTuple (map (ppIdent env .snd) (nShows node))
            )
  $$ text "let"
  $$ nest 2 (vcatSep (map (ppEqnGroup env) (nEqns node)))
  $$ text "tel"
  where
  env = identVariants node



-- | Pick a normalized number for the identifier in a node.
-- Identifiers with the same text name are going to get different numbers.
-- Identifiers that only have one version around will get the number 0.
-- This is handy for pretty printing and exporting to external tools.
identVariants :: Node -> Map Ident Int
identVariants node = Map.fromList
                   $ concat
                   $ Map.elems
                   $ fmap (`zip` [ 0 .. ])
                   $ Map.fromListWith (++)
                   $ map binderInfo
                   $ nInputs node ++ [ b | g <- nEqns node, b := _ <- grpEqns g]

  where
  binderInfo (x ::: _) = (identText x, [x])




instance Pretty Op where
  ppPrec _ = ppPrim

instance Pretty Type where
  ppPrec _ = ppType

instance Pretty CType where
  ppPrec _ = ppCType noInfo

instance Pretty Binder where
  ppPrec _ = ppBinder noInfo

instance Pretty Atom where
  ppPrec _ = ppAtom noInfo

instance Pretty Expr where
  ppPrec _ = ppExpr noInfo

instance Pretty Eqn where
  ppPrec _ = ppEqn noInfo

instance Pretty Node where
  ppPrec _ = ppNode


--------------------------------------------------------------------------------
-- Computing the the type of an expression.


-- | Compute the typing environment for a node.
nodeEnv :: Node -> Map Ident CType
nodeEnv nd = Map.fromList $ map fromB (nInputs nd) ++
                            map fromE (concatMap grpEqns (nEqns nd))
  where
  fromB (x ::: t) = (x,t)
  fromE (b := _)  = fromB b

clockParent :: Map Ident CType -> Clock -> Maybe Clock
clockParent env c =
  case c of
    BaseClock -> Nothing
    WhenTrue a -> Just (clockOfCType (typeOf env a))

class TypeOf t where
  -- | Get the type of something well-formed (panics if not).
  typeOf :: Map Ident CType -> t -> CType

instance TypeOf Atom where
  typeOf env atom =
    case atom of
      Var x -> case Map.lookup x env of
                 Just t -> t
                 Nothing -> panic "typeOf" ["Undefined variable: " ++ showPP x]
      Lit _ ty -> ty

      Prim op as  ->
        case as of
          a : _ ->
             let t `On` c = typeOf env a
                 ret x = x `On` c
             in case op of
                  IntCast    -> ret TInt
                  FloorCast  -> ret TInt
                  RealCast   -> ret TReal

                  Not        -> ret TBool
                  And        -> ret TBool
                  Or         -> ret TBool
                  Xor        -> ret TBool
                  Implies    -> ret TBool
                  Eq         -> ret TBool
                  Neq        -> ret TBool
                  Lt         -> ret TBool
                  Leq        -> ret TBool
                  Gt         -> ret TBool
                  Geq        -> ret TBool
                  AtMostOne  -> ret TBool
                  Nor        -> ret TBool

                  Neg        -> ret t
                  Mul        -> ret t
                  Mod        -> ret t
                  Div        -> ret t
                  Add        -> ret t
                  Sub        -> ret t
                  Power      -> ret t

                  ITE        -> case as of
                                  _ : b : _ -> typeOf env b
                                  _ -> panic "typeOf" ["Malformed ITE"]
          _ -> panic "typeOf" ["0 arity prim: " ++ showPP op]



instance TypeOf Expr where
  typeOf env expr =
    case expr of
      Atom a      -> typeOf env a
      a :-> _     -> typeOf env a
      Pre a       -> typeOf env a
      a `When` b  -> let t `On` _ = typeOf env a
                     in t `On` WhenTrue b
      Current a   -> let t `On` c  = typeOf env a
                         Just c1   = clockParent env c
                      in t `On` c1
      Merge c b _ -> let _ `On` c1 = typeOf env c
                         t `On` _  = typeOf env b
                      in t `On` c1

