{-# Language OverloadedStrings #-}
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

import Language.Lustre.AST (Literal(..))
import Language.Lustre.Pretty

data Ident    = Ident Text
                deriving (Show,Eq,Ord)

-- XXX: Support for integer ranges.
-- This would be useful to model enums, as well as "subrange [x,y] of int"
data Type     = TInt | TReal | TBool
                deriving Show

-- | A boolean clock.  The base clock is always @true@.
type Clock    = Atom

-- | Type on a boolean clock.
data CType    = Type `On` Clock
                deriving Show

data Binder   = Ident ::: CType
                deriving Show

data Atom     = Lit Literal
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
infix 2 :::
infix 3 `On`

data Node     = Node { nInputs      :: [Binder]
                     , nOutputs     :: [Ident]
                     , nAssuming    :: [(Text,Ident)]
                       -- ^ Assuming that these are true (Text is a label)
                     , nShows       :: [(Text,Ident)]
                       -- ^ Need to show that these are also true
                       -- (Text is a label)
                     , nEqns        :: [Eqn]
                     } deriving Show




--------------------------------------------------------------------------------
-- Ordering equations

usesAtom :: Atom -> Set Ident
usesAtom atom =
  case atom of
    Lit _     -> Set.empty
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

-- | Order the equations.  Returns cycles on the left, if there are some.
orderedEqns :: [Eqn] -> Either [ [Binder] ] [ Eqn ]
orderedEqns eqns
  | null bad  = Right good
  | otherwise = Left bad
  where
  graph = [ (eqn, x, Set.toList (Set.union (usesAtom c) (usesExpr e)))
              | eqn <- eqns, let (x ::: _ `On` c) := e = eqn ]

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

ppCType :: CType -> Doc
ppCType (t `On` c) =
  case c of
    Lit (Bool True) -> ppType t
    _ -> ppType t <+> "when" <+> ppAtom c

ppBinder :: Binder -> Doc
ppBinder (x ::: t) = ppIdent x <+> text ":" <+> ppCType t

ppAtom :: Atom -> Doc
ppAtom atom =
  case atom of
    Lit l -> pp l
    Var x -> ppIdent x
    Prim f as   -> ppPrim f PP.<> ppTuple (map ppAtom as)

ppExpr :: Expr -> Doc
ppExpr expr =
  case expr of
    Atom a      -> ppAtom a
    a :-> b     -> ppAtom a <+> text "->" <+> ppAtom b
    Pre a       -> text "pre" <+> ppAtom a
    a `When` b  -> ppAtom a <+> text "when" <+> ppAtom b
    Current a   -> text "current" <+> ppAtom a
    Merge a b c -> text "merge" <+> ppAtom a <+> ppAtom b <+> ppAtom c


ppTuple :: [Doc] -> Doc
ppTuple ds = parens (hsep (punctuate comma ds))

ppEqn :: Eqn -> Doc
ppEqn (x ::: t := e) =
  ppIdent x <+> "=" <+> ppExpr e <+> "//" <+> ppCType t

ppNode :: Node -> Doc
ppNode node =
  text "node" <+> ppTuple (map ppBinder (nInputs node))
  $$ nest 2 (  text "returns" <+> ppTuple (map ppIdent (nOutputs node))
            $$ text "assumes" <+> ppTuple (map (ppIdent.snd) (nAssuming node))
            $$ text "shows" <+> ppTuple (map (ppIdent.snd) (nShows node))
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

instance Pretty CType where
  ppPrec _ = ppCType

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
  typeOf :: Map Ident CType -> t -> Maybe CType

-- XXX: These seem to have "polymorphic clocks"
instance TypeOf Literal where
  typeOf _ lit =
    Just $
    case lit of
      Int _  -> base TInt
      Real _ -> base TReal
      Bool _ -> base TBool
    where base t = t `On` Lit (Bool True)

instance TypeOf Atom where
  typeOf env atom =
    case atom of
      Var x -> Map.lookup x env
      Lit l -> typeOf env l
      Prim op as  ->
        case as of
          a : _ ->
            do (t `On` c) <- typeOf env a
               let ret x = Just (x `On` c)
               case op of
                 IntCast    -> ret TInt
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
                                 _ -> Nothing
          _ -> Nothing




instance TypeOf Expr where
  typeOf env expr =
    case expr of
      Atom a      -> typeOf env a
      a :-> _     -> typeOf env a
      Pre a       -> typeOf env a
      a `When` b  -> do t `On` _ <- typeOf env a
                        pure (t `On` b)
      Current a   -> do t `On` c  <- typeOf env a
                        _ `On` c1 <- typeOf env c
                        pure (t `On` c1)
      Merge c b _ -> do _ `On` c1 <- typeOf env c
                        t `On` _  <- typeOf env b
                        pure (t `On` c1)

