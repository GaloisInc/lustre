{-# Language OverloadedStrings #-}
module Language.Lustre.Pretty where

import Data.Text (Text)
import qualified Data.Text as Text
import Text.PrettyPrint hiding ( (<>) )
import qualified Text.PrettyPrint as PP
import Numeric(showGFloat)
import Data.Ratio(numerator,denominator)

import Language.Lustre.AST

class Pretty t where
  ppPrec :: Int -> t -> Doc

pp :: Pretty t => t -> Doc
pp = ppPrec 0


{-
instance Pretty TopDecl where
  ppPrec n td =
    case td of
      DeclareType td      -> ppPrec n td
      DeclareConst cd     -> ppPrec n cd
      DeclareNode nd      -> ppPrec n nd
      DeclareNodeInst nid -> ppPrec n nid
-}

instance Pretty Text where
  ppPrec _ = text . Text.unpack

instance Pretty Ident where
  ppPrec n i = ppPrec n (identText i)

instance Pretty Name where
  ppPrec n nam =
    case nam of
      Unqual i   -> ppPrec n i
      Qual _ x y -> ppPrec n x PP.<> "::" PP.<> ppPrec n y

instance Pretty TypeDecl where
  ppPrec _ t = "type" <+> pp (typeName t) <+> mbDef
    where mbDef = case typeDef t of
                    Nothing -> semi
                    Just d  -> "=" <+> pp d PP.<> semi

instance Pretty TypeDef where
  ppPrec _ td =
    case td of
      IsType t    -> pp t
      IsEnum is   -> "enum" <+> braces (hsep (punctuate comma (map pp is)))
      IsStruct fs -> braces (vcat (punctuate semi (map pp fs)))

instance Pretty FieldType where
  ppPrec _ ft = pp (fieldName ft) <+> pp (fieldType ft) <+> optVal
    where optVal = case fieldDefault ft of
                     Nothing -> empty
                     Just e  -> "=" <+> pp e

instance Pretty Type where
  ppPrec n ty =
    case ty of
      NamedType x   -> pp x
      ArrayType t e -> pp t <+> "^" <+> pp e      -- precedence?
      IntType       -> "int"
      RealType      -> "real"
      BoolType      -> "bool"
      TypeRange _ t -> ppPrec n t

instance Pretty Literal where
  ppPrec _ lit =
    case lit of
      Int n  -> integer n
      Bool b -> if b then "true" else "false"
      Real r | toRational t == r -> text (showGFloat Nothing t "")
             | otherwise -> parens (sh (numerator r) <+> "/" <+>
                                    sh (denominator r))
        where
        t    = fromRational r :: Double
        sh x = integer x <> ".0"

{-
Precedences:
1    %left     '|'
2    %nonassoc '->'
3    %right    '=>'
4    %left     'or' 'xor'
5    %left     'and'
6    %nonassoc '<' '<=' '=' '>=' '>' '<>'
7    %nonassoc 'not'                      PREF
8    %left     '+' '-'
9    %left     '*' '/' '%' 'mod' 'div'
10   %left     '**'
11   %nonassoc 'when'
12   %nonassoc 'int' 'real'               PREF
13   %nonassoc UMINUS 'pre' 'current'     PREF
14   %left     '^' '.'
15   %right    '['
-}
instance Pretty Expression where
  ppPrec n expr =
    case expr of
      ERange _ e    -> ppPrec n e
      Var x         -> pp x
      Lit l         -> pp l
      EOp1 op e     -> parenIf (n >= p) doc
        where doc = pp op <> ppPrec p e
              p   = case op of
                      Not      -> 7
                      IntCast  -> 12
                      RealCast -> 12
                      Neg      -> 13
                      Pre      -> 13
                      Current  -> 13

      EOp2 e1 op e2 -> parenIf (n > p) doc
        where doc = ppPrec lp e1 <+> pp op <+> ppPrec rp e2
              (lp,p,rp) = case op of
                            Concat  -> (0,0,1)
                            Fby     -> (2,1,2)
                            Implies -> (3,2,2)
                            Or      -> (3,3,4)
                            Xor     -> (3,3,4)
                            And     -> (4,4,5)
                            Lt      -> (6,5,6)
                            Leq     -> (6,5,6)
                            Gt      -> (6,5,6)
                            Geq     -> (6,5,6)
                            Eq      -> (6,5,6)
                            Neq     -> (6,5,6)
                            Add     -> (7,7,8)
                            Sub     -> (7,7,8)
                            Mul     -> (8,8,9)
                            Div     -> (8,8,9)
                            Mod     -> (8,8,9)
                            Power   -> (9,9,10)
                            Replicate -> (13,13,14)

      e `When` ce   -> parenIf (n > 10) doc
        where doc = ppPrec 11 e <+> "when" <+> ppPrec 11 ce

      EOpN op es    -> pp op <> parens (hsep (punctuate comma (map pp es)))

      Tuple es      -> parens (hsep (punctuate comma (map pp es)))
      Array es      -> brackets (hsep (punctuate comma (map pp es)))
      Select e s    -> ppPrec 13 e <> pp s
      Struct s mb fs ->
        pp s <+> braces (mbWith <+> vcat (punctuate semi (map pp fs)))
          where mbWith = case mb of
                           Nothing -> mempty
                           Just x  -> pp x <+> "with"


      IfThenElse e1 e2 e3  -> parenIf (n > 0) doc
        where doc = "if" <+> pp e1 $$ nest 2 ("then" <+> ppPrec 0 e2)
                                   $$ nest 2 ("else" <+> ppPrec 0 e3)

      WithThenElse e1 e2 e3 -> parenIf (n > 0) doc
        where doc = "with" <+> pp e1 $$ nest 2 ("then" <+> ppPrec 0 e2)
                                     $$ nest 2 ("else" <+> ppPrec 0 e3)

      Merge i as  -> parenIf (n > 1) doc
        where doc = "merge" <+> pp i $$ nest 2 (vcat (map pp as))

      CallPos f es ->
        pp f <+> parens (hsep (punctuate comma (map pp es)))

parenIf :: Bool -> Doc -> Doc
parenIf p d = if p then parens d else d


instance Pretty MergeCase where
  ppPrec _ (MergeCase cv e) = parens (pp cv <+> "->" <+> pp e)

instance Pretty ClockVal where
  ppPrec _ cv =
    case cv of
      ClockIsTrue   -> "true"
      ClockIsFalse  -> "false"
      ClockIs x     -> pp x

instance Pretty Field where
  ppPrec _ (Field x e) = pp x <+> "=" <+> pp e

instance Pretty e => Pretty (Selector e) where
  ppPrec _ sel =
    case sel of
      SelectField i       -> "." <> pp i
      SelectElement e     -> brackets (pp e)
      SelectSlice e       -> brackets (pp e)

instance Pretty e => Pretty (ArraySlice e) where
  ppPrec _ as = pp (arrayStart as) <+> ".." <+> pp (arrayEnd as) <+> mbStep
    where mbStep = case arrayStep as of
                     Nothing -> empty
                     Just e  -> "step" <+> pp e

instance Pretty ClockExpr where
  ppPrec _ (WhenClock _ cv i) =
    case cv of
      ClockIsTrue   -> pp i
      ClockIsFalse  -> "not" <+> pp i
      ClockIs x     -> pp x <> parens (pp i)

instance Pretty NodeInst where
  ppPrec _ (NodeInst x as) =
    case as of
      [] -> pp x
      _  -> pp x <+> "<<" PP.<> hsep (punctuate comma (map pp as)) PP.<> ">>"

instance Pretty StaticArg where
  ppPrec n arg =
    case arg of
      TypeArg t     -> "type" <+> pp t
      ExprArg e     -> "const" <+> pp e
      NodeArg nf x  -> pp nf <+> pp x
      Op1Arg op     -> pp op
      Op2Arg op     -> pp op
      OpIf          -> "if"
      ArgRange _ a  -> ppPrec n a

instance Pretty NodeType where
  ppPrec _ nt =
    case nt of
      Node     -> "node"
      Function -> "function"

instance Pretty Op1 where
  ppPrec _ op =
    case op of
      Not       -> "not"
      Neg       -> "-"
      Pre       -> "pre"
      Current   -> "current"
      IntCast   -> "int"
      RealCast  -> "real"

instance Pretty Op2 where
  ppPrec _ op =
    case op of
      Fby         -> "->"
      And         -> "and"
      Or          -> "or"
      Xor         -> "xor"
      Implies     -> "=>"
      Eq          -> "="
      Neq         -> "<>"
      Lt          -> "<"
      Leq         -> "<="
      Gt          -> ">"
      Geq         -> ">="
      Mul         -> "*"
      Mod         -> "mod"
      Div         -> "/"
      Add         -> "+"
      Sub         -> "-"
      Power       -> "**"
      Replicate   -> "^"
      Concat      -> "|"

instance Pretty OpN where
  ppPrec _ op =
    case op of
      AtMostOne   -> "#"
      Nor         -> "nor"



