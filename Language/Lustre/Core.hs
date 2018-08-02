module Language.Lustre.Core
  (module Language.Lustre.Core, Literal(..)) where

import Data.Text(Text)
import qualified Data.Text as Text
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC
import Text.PrettyPrint(Doc, integer, text, (<+>), ($$), nest, vcat, hsep
                       , parens, punctuate, comma )
import qualified Text.PrettyPrint as PP

import Language.Lustre.AST (Literal(..))

data Ident    = Ident Text
                deriving (Show,Eq,Ord)

data Name     = Name String
                deriving Show

data Atom     = ALit Literal
              | AVar Ident
                deriving Show

data Expr     = EAtom Atom
              | EFby Atom Atom
              | EPre Atom
              | EWhen Atom Atom
              | ECurrent Atom
              | ECall Name [Atom]
                deriving Show

data Eqn      = Eqn Ident Expr
                deriving Show


--------------------------------------------------------------------------------
usesAtom :: Atom -> Set Ident
usesAtom atom =
  case atom of
    ALit _ -> Set.empty
    AVar x -> Set.singleton x

usesExpr :: Expr -> Set Ident
usesExpr expr =
  case expr of
    EAtom a     -> usesAtom a
    EFby a1 a2  -> Set.union (usesAtom a1) (usesAtom a2)
    EPre _      -> Set.empty -- refer to values at previous instance
    EWhen a1 a2 -> Set.union (usesAtom a1) (usesAtom a2)
    ECurrent a  -> usesAtom a
    ECall _ as  -> Set.unions (map usesAtom as)

-- | Order the equations.  Returns a cycles on the left, if there are some.
orderedEqns :: [Eqn] -> Either [ [Ident] ] [ Eqn ]
orderedEqns eqns
  | null bad  = Right good
  | otherwise = Left bad
  where
  graph = map toNode eqns
  toNode eqn@(Eqn x e) = (eqn, x, Set.toList (usesExpr e))

  comps = stronglyConnComp graph

  bad   = [ [ x | Eqn x _ <- xs ] | CyclicSCC xs <- comps ]
  good  = [ x | AcyclicSCC x <- comps ]


--------------------------------------------------------------------------------
ppIdent :: Ident -> Doc
ppIdent (Ident x) = text (Text.unpack x)

ppName :: Name -> Doc
ppName (Name x) = text x

ppLiteral :: Literal -> Doc
ppLiteral lit =
  case lit of
    Int n  -> integer n
    Real n -> text (show n)
    Bool b -> text (show b)

ppAtom :: Atom -> Doc
ppAtom atom =
  case atom of
    ALit l -> ppLiteral l
    AVar x -> ppIdent x

ppExpr :: Expr -> Doc
ppExpr expr =
  case expr of
    EAtom a     -> ppAtom a
    EFby a1 a2  -> ppAtom a1 <+> text "->" <+> ppAtom a2
    EPre a1     -> text "pre" <+> ppAtom a1
    EWhen a1 a2 -> ppAtom a1 <+> text "when" <+> ppAtom a2
    ECurrent a  -> text "current" <+> ppAtom a
    ECall f xs  ->
      ppName f PP.<> parens (hsep (punctuate comma (map ppAtom xs)))

ppEqn :: Eqn -> Doc
ppEqn (Eqn x e) = ppIdent x <+> text "=" <+> ppExpr e

ppEqnSCC :: SCC Eqn -> Doc
ppEqnSCC eqSCC =
  case eqSCC of
    AcyclicSCC eqn -> ppEqn eqn
    CyclicSCC eqns -> text "rec" $$ nest 2 (vcat (map ppEqn eqns))

