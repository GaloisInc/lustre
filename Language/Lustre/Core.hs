module Language.Lustre.Core
  (module Language.Lustre.Core, Literal(..)) where

import Data.Text(Text)
import qualified Data.Text as Text
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import Text.PrettyPrint( Doc, text, (<+>)
                       , hsep, vcat, nest, parens, punctuate, comma, ($$) )
import qualified Text.PrettyPrint as PP
import Control.Monad(msum)

import Language.Lustre.AST (Literal(..))
import Language.Lustre.Pretty

data Ident    = Ident Text
                deriving (Show,Eq,Ord)

-- XXX: Support for integer ranges.
-- This would be useful to model enums, as well as "subrange [x,y] of int"
data Type     = TInt | TReal | TBool
                deriving Show

data Binder   = Ident ::: Type
                deriving Show

data Atom     = Lit Literal
              | Var Ident
                deriving Show

data Expr     = Atom Atom
              | Atom :-> Atom
              | Pre Atom
              | Atom `When` Atom
              | Current Atom
              | Prim Op [Atom]
                deriving Show

data Op       = Not | Neg
              | IntCast | RealCast
              | And | Or | Xor | Implies
              | Eq | Neq | Lt | Leq | Gt | Geq
              | Mul | Mod | Div | Add | Sub | Power
              | ITE
              | AtMostOne | Nor
                deriving Show

data Eqn      = Binder := Expr
                deriving Show

infix 1 :=

data Node     = Node { nInputs      :: [Binder]
                     , nOutputs     :: [Ident]
                     , nAssuming    :: [Ident]
                       -- ^ Assuming that these are true
                     , nShows       :: [Ident]
                       -- ^ Need to show that these are also true
                     , nEqns        :: [Eqn]
                     } deriving Show




--------------------------------------------------------------------------------
-- Ordering equations

usesAtom :: Atom -> Set Ident
usesAtom atom =
  case atom of
    Lit _ -> Set.empty
    Var x -> Set.singleton x

usesExpr :: Expr -> Set Ident
usesExpr expr =
  case expr of
    Atom a        -> usesAtom a
    a1 :-> a2     -> Set.union (usesAtom a1) (usesAtom a2)
    Pre _         -> Set.empty -- refer to values at previous instance
    a1 `When` a2  -> Set.union (usesAtom a1) (usesAtom a2)
    Current a     -> usesAtom a
    Prim _ as     -> Set.unions (map usesAtom as)

-- | Order the equations.  Returns cycles on the left, if there are some.
orderedEqns :: [Eqn] -> Either [ [Binder] ] [ Eqn ]
orderedEqns eqns
  | null bad  = Right good
  | otherwise = Left bad
  where
  graph = [ (eqn, x, Set.toList (usesExpr e))
              | eqn <- eqns, let (x ::: _) := e = eqn ]

  comps = stronglyConnComp graph

  bad   = [ [ x | x := _ <- xs ] | CyclicSCC xs <- comps ]
  good  = [ x | AcyclicSCC x <- comps ]


--------------------------------------------------------------------------------
-- Pretty Printing

ppIdent :: Ident -> Doc
ppIdent (Ident x) = text (Text.unpack x)

ppPrim :: Op -> Doc
ppPrim = text . show

ppType :: Type -> Doc
ppType ty =
  case ty of
    TInt  -> text "int"
    TReal -> text "real"
    TBool -> text "bool"

ppBinder :: Binder -> Doc
ppBinder (x ::: t) = ppIdent x <+> text ":" <+> ppType t

ppAtom :: Atom -> Doc
ppAtom atom =
  case atom of
    Lit l -> pp l
    Var x -> ppIdent x

ppExpr :: Expr -> Doc
ppExpr expr =
  case expr of
    Atom a      -> ppAtom a
    a :-> b     -> ppAtom a <+> text "->" <+> ppAtom b
    Pre a       -> text "pre" <+> ppAtom a
    a `When` b  -> ppAtom a <+> text "when" <+> ppAtom b
    Current a   -> text "current" <+> ppAtom a
    Prim f as   -> ppPrim f PP.<> ppTuple (map ppAtom as)


ppTuple :: [Doc] -> Doc
ppTuple ds = parens (hsep (punctuate comma ds))

ppEqn :: Eqn -> Doc
ppEqn (x := e) = ppBinder x <+> text "=" <+> ppExpr e

ppNode :: Node -> Doc
ppNode node =
  text "node" <+> ppTuple (map ppBinder (nInputs node))
  $$ nest 2 (  text "returns" <+> ppTuple (map ppIdent (nOutputs node))
            $$ text "assumes" <+> ppTuple (map ppIdent (nAssuming node))
            $$ text "shows" <+> ppTuple (map ppIdent (nShows node))
            )
  $$ text "let"
  $$ nest 2 (vcat (map ppEqn (nEqns node)))
  $$ text "tel"

instance Pretty Ident where
  ppPrec _ = ppIdent

instance Pretty Op where
  ppPrec _ = ppPrim

instance Pretty Type where
  ppPrec _ = ppType

instance Pretty Binder where
  ppPrec _ = ppBinder

instance Pretty Atom where
  ppPrec _ = ppAtom

instance Pretty Expr where
  ppPrec _ = ppExpr

instance Pretty Eqn where
  ppPrec _ = ppEqn

instance Pretty Node where
  ppPrec _ = ppNode


--------------------------------------------------------------------------------
-- Computing the the type of an expression.

class TypeOf t where
  typeOf :: Map Ident Type -> t -> Maybe Type

instance TypeOf Literal where
  typeOf _ lit =
    Just $
    case lit of
      Int _  -> TInt
      Real _ -> TReal
      Bool _ -> TBool

instance TypeOf Atom where
  typeOf env atom =
    case atom of
      Var x -> Map.lookup x env
      Lit l -> typeOf env l

instance TypeOf Expr where
  typeOf env expr =
    case expr of
      Atom a      -> typeOf env a
      a :-> _     -> typeOf env a
      Pre a       -> typeOf env a
      a `When` _  -> typeOf env a
      Current a   -> typeOf env a
      Prim op as  ->
        case as of
          a : _ ->
            let t    = typeOf env a
                bool = Just TBool
            in case op of
                 IntCast    -> Just TInt
                 RealCast   -> Just TReal

                 Not        -> bool
                 And        -> bool
                 Or         -> bool
                 Xor        -> bool
                 Implies    -> bool
                 Eq         -> bool
                 Neq        -> bool
                 Lt         -> bool
                 Leq        -> bool
                 Gt         -> bool
                 Geq        -> bool
                 AtMostOne  -> bool
                 Nor        -> bool

                 Neg        -> t
                 Mul        -> t
                 Mod        -> t
                 Div        -> t
                 Add        -> t
                 Sub        -> t
                 Power      -> t

                 ITE        -> case as of
                                 _ : b : _ -> typeOf env b
                                 _ -> Nothing
          _ -> Nothing

type Clock = Atom

baseClock :: Clock
baseClock = Lit (Bool True)

class ClockOf t where
  clockOf :: Map Ident Clock -> t -> Maybe Clock

instance ClockOf Atom where
  clockOf clocks atom =
    case atom of
      Lit _ -> Just baseClock
      Var x -> Map.lookup x clocks

instance ClockOf Expr where
  clockOf clocks expr =
    case expr of
      Atom a     -> atom a
      a :-> b    -> msum [ atom a, atom b]  -- should be the saem
      Pre a      -> atom a
      _ `When` b -> Just b
      Current a  -> atom =<< atom a
      Prim _ as  -> msum (map atom as)  -- any of those should be the same
    where
    atom = clockOf clocks

-- | Compute the clocks for all variables defined in the node.
computeClocks :: Node -> Maybe (Map Ident Clock)
computeClocks node = go False [] clocks0 (nEqns node)
  where
  -- XXX: Annotate inputs with clocks.
  clocks0 = Map.fromList [ (x,baseClock) | x ::: _ <- nInputs node ]

  -- We do this iteratively because the dependency story is a bit
  -- convoluted due to the presence of "pre".
  go changes todo clocks eqns =
    case eqns of
      [] ->
        case todo of
          [] -> Just clocks
          _  -> if changes then go False [] clocks todo else Nothing
      eqn@(x ::: _ := e) : more ->
        case clockOf clocks e of
          Just c  -> go True todo (Map.insert x c clocks) more
          Nothing -> go changes (eqn : todo) clocks more


