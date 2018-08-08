module Language.Lustre.Core
  (module Language.Lustre.Core, Literal(..)) where

import Data.Text(Text)
import qualified Data.Text as Text
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import Text.PrettyPrint( Doc, integer, text, (<+>)
                       , hsep, vcat, nest, parens, punctuate, comma, ($$) )
import qualified Text.PrettyPrint as PP

import Language.Lustre.AST (Literal(..))

data Ident    = Ident Text
                deriving (Show,Eq,Ord)

data Name     = Name Text
                deriving (Show,Eq,Ord)

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
              | Call Name [Atom]
                deriving Show

data Eqn      = Binder := Expr
                deriving Show

infix 1 :=

data Node     = Node { nName    :: Name
                     , nInputs  :: [Binder]
                     , nOutputs :: [Ident]
                     , nAsserts :: [Ident]
                     , nEqns    :: [Eqn]    -- ^ In dependency order
                     } deriving Show




--------------------------------------------------------------------------------
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
    Call _ as     -> Set.unions (map usesAtom as)

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
ppIdent :: Ident -> Doc
ppIdent (Ident x) = text (Text.unpack x)

ppName :: Name -> Doc
ppName (Name x) = text (Text.unpack x)

ppType :: Type -> Doc
ppType ty =
  case ty of
    TInt  -> text "int"
    TReal -> text "real"
    TBool -> text "bool"

ppBinder :: Binder -> Doc
ppBinder (x ::: t) = ppIdent x <+> text ":" <+> ppType t

ppLiteral :: Literal -> Doc
ppLiteral lit =
  case lit of
    Int n  -> integer n
    Real n -> text (show n)
    Bool b -> text (show b)

ppAtom :: Atom -> Doc
ppAtom atom =
  case atom of
    Lit l -> ppLiteral l
    Var x -> ppIdent x

ppExpr :: Expr -> Doc
ppExpr expr =
  case expr of
    Atom a      -> ppAtom a
    a :-> b     -> ppAtom a <+> text "->" <+> ppAtom b
    Pre a       -> text "pre" <+> ppAtom a
    a `When` b  -> ppAtom a <+> text "when" <+> ppAtom b
    Current a   -> text "current" <+> ppAtom a
    Call f as   -> ppName f PP.<> ppTuple (map ppAtom as)

ppTuple :: [Doc] -> Doc
ppTuple ds = parens (hsep (punctuate comma ds))

ppEqn :: Eqn -> Doc
ppEqn (x := e) = ppBinder x <+> text "=" <+> ppExpr e

ppNode :: Node -> Doc
ppNode node =
  text "node" <+> ppName (nName node) <+> ppTuple (map ppBinder (nInputs node))
  $$ nest 2 (  text "returns" <+> ppTuple (map ppIdent (nOutputs node))
            $$ text "asserts" <+> ppTuple (map ppIdent (nAsserts node))
            )
  $$ text "let"
  $$ nest 2 (vcat (map ppEqn (nEqns node)))
  $$ text "tel"



--------------------------------------------------------------------------------

