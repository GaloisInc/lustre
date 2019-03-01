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
                       , hsep, vcat, nest, parens, punctuate, comma, ($$) )
import qualified Text.PrettyPrint as PP

import Language.Lustre.AST (Literal(..),PropName(..))
import Language.Lustre.Name
import Language.Lustre.Pretty
import Language.Lustre.Panic(panic)

{-
data Ident    = Ident Text
                deriving (Show,Eq,Ord)
-}

-- XXX: Support for integer ranges.
-- This would be useful to model enums, as well as "subrange [x,y] of int"
data Type     = TInt | TReal | TBool
                deriving Show

-- | A boolean clock.  The base clock is always @true@.
type Clock    = Atom

-- | Type on a boolean clock.
data CType    = Type `On` Clock
                deriving Show

typeOfCType :: CType -> Type
typeOfCType (t `On` _) = t

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


type PPInfo = Set Ident -- These idents are safe and no need to show unique

noInfo :: PPInfo
noInfo = Set.empty

ppPrim :: Op -> Doc
ppPrim = text . show

ppIdent :: PPInfo -> Ident -> Doc
ppIdent info i
  | i `Set.member` info = pp i
  | otherwise = pp (identText i) PP.<> "_" PP.<> PP.int (identUID i)

ppType :: Type -> Doc
ppType ty =
  case ty of
    TInt  -> text "int"
    TReal -> text "real"
    TBool -> text "bool"

ppCType :: PPInfo -> CType -> Doc
ppCType env (t `On` c) =
  case c of
    Lit (Bool True) -> ppType t
    _ -> ppType t <+> "when" <+> ppAtom env c

ppBinder :: PPInfo -> Binder -> Doc
ppBinder env (x ::: t) = ppIdent env x <+> text ":" <+> ppCType env t

ppAtom :: PPInfo -> Atom -> Doc
ppAtom env atom =
  case atom of
    Lit l -> pp l
    Var x -> ppIdent env x
    Prim f as   -> ppPrim f PP.<> ppTuple (map (ppAtom env) as)

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
ppEqn env (x ::: t := e) =
  ppIdent env x <+> "=" <+> ppExpr env e -- <+> "//" <+> ppCType env t

ppNode :: Node -> Doc
ppNode node =
  text "node" <+> ppTuple (map (ppBinder env) (nInputs node))
  $$ nest 2 (  text "returns" <+> ppTuple (map (ppIdent env) (nOutputs node))
            $$ text "assumes" <+> ppTuple (map (ppIdent env . snd)
                                                (nAssuming node))
            $$ text "shows" <+> ppTuple (map (ppIdent env .snd) (nShows node))
            )
  $$ text "let"
  $$ nest 2 (vcat (map (ppEqn env) (nEqns node)))
  $$ text "tel"
  where env = nodePPInfo node

nodePPInfo :: Node -> PPInfo
nodePPInfo node =
  Set.fromList
    [ i | [i] <- Map.elems $ Map.fromListWith (++)
                           $ map binderInfo
                           $ nInputs node ++
                             [ b | b := _ <- nEqns node ]
    ]

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
nodeEnv nd = Map.fromList $ map fromB (nInputs nd) ++ map fromE (nEqns nd)
  where
  fromB (x ::: t) = (x,t)
  fromE (b := _)  = fromB b


class TypeOf t where
  -- | Get the type of something well-formed (panics if not).
  typeOf :: Map Ident CType -> t -> CType

-- XXX: These seem to have "polymorphic clocks"
instance TypeOf Literal where
  typeOf _ lit =
    case lit of
      Int _  -> base TInt
      Real _ -> base TReal
      Bool _ -> base TBool
    where base t = t `On` Lit (Bool True)

instance TypeOf Atom where
  typeOf env atom =
    case atom of
      Var x -> case Map.lookup x env of
                 Just t -> t
                 Nothing -> panic "typeOf" ["Undefined variable: " ++ showPP x]
      Lit l -> typeOf env l
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
                     in t `On` b
      Current a   -> let t `On` c  = typeOf env a
                         _ `On` c1 = typeOf env c
                      in t `On` c1
      Merge c b _ -> let _ `On` c1 = typeOf env c
                         t `On` _  = typeOf env b
                      in t `On` c1

