{-# Language OverloadedStrings #-}
module Language.Lustre.Pretty where

import Data.Text (Text)
import Data.List(intersperse)
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

vcatSep :: [Doc] -> Doc
vcatSep = vcat . intersperse " "


instance Pretty Text where
  ppPrec _ = text . Text.unpack

instance Pretty Ident where
  ppPrec n i = ppPrec n (identText i)

instance Pretty Name where
  ppPrec n nam =
    case nam of
      Unqual i   -> ppPrec n i
      Qual _ x y -> ppPrec n x PP.<> "::" PP.<> ppPrec n y

--------------------------------------------------------------------------------


instance Pretty TopDecl where
  ppPrec n td =
    case td of
      DeclareType dt      -> ppPrec n dt
      DeclareConst cd     -> ppPrec n cd <> semi
      DeclareNode nd      -> ppPrec n nd
      DeclareNodeInst nid -> ppPrec n nid

instance Pretty ConstDef where
  ppPrec _ def = "const" <+> pp (constName def) <+>
                  opt ":" (constType def) <+>
                  opt "=" (constDef def)
    where
    opt x y = case y of
                Nothing -> empty
                Just a  -> x <+> pp a

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

instance Pretty NodeInstDecl where
  ppPrec _ nid =
    ppSafetyOpt (nodeInstSafety nid) <+>
    pp (nodeInstType nid) <+>
    pp (nodeInstName nid) <+>
    ppSaticParams (nodeInstStaticInputs nid) <+>
    profDoc <+>
    "=" <+> pp (nodeInstDef nid) PP.<> semi
    where
    profDoc =
      case nodeInstProfile nid of
        Nothing -> empty
        Just p  -> pp p

ppSaticParams :: [StaticParam] -> Doc
ppSaticParams xs =
  case xs of
    [] -> empty
    _  -> "<<" PP.<> hsep (punctuate semi (map pp xs)) PP.<> ">>"

instance Pretty NodeProfile where
  ppPrec _ np =
    parens (hsep (punctuate semi (map pp (nodeInputs np)))) <+>
    "returns" <+> parens (hsep (punctuate semi (map pp (nodeOutputs np))))

instance Pretty Binder where
  ppPrec _ b = pp (binderDefines b) <+> ":" <+> pp (binderType b) <+> clockDoc
    where clockDoc = case binderClock b of
                       Nothing -> empty
                       Just c  -> "when" <+> pp c

instance Pretty StaticParam where
  ppPrec _ sp =
    case sp of
      TypeParam i         -> "type" <+> pp i
      ConstParam i t      -> "const" <+> pp i <+> ":" <+> pp t
      NodeParam s nt f p  -> ppSafetyOpt s <+> pp nt <+> pp f <+> pp p


instance Pretty NodeDecl where
  ppPrec _ nd =
    ppSafetyOpt (nodeSafety nd) <+>
    (if nodeExtern nd then "extern" else empty) <+>
    pp (nodeType nd) <+>
    pp (nodeName nd) <+>
    ppSaticParams (nodeStaticInputs nd) <+>
    pp (nodeProfile nd) $$
    bodyDoc
    where bodyDoc = case nodeDef nd of
                      Nothing -> semi
                      Just x  -> pp x

instance Pretty NodeBody where
  ppPrec _ nb =
    vcat [ pp d <> semi | d <- nodeLocals nb ] $$
    "let" $$
    nest 2 (vcat [ pp d <> semi | d <- nodeEqns nb ]) $$
    "tel"

instance Pretty LocalDecl where
  ppPrec _ ld =
    case ld of
      LocalVar b   -> "var" <+> pp b
      LocalConst c -> "const" <+> pp c

instance Pretty Equation where
  ppPrec _ eqn =
    case eqn of
      Assert e -> "assert" <+> pp e
      Define ls e -> hsep (punctuate comma (map pp ls)) <+> "=" <+> pp e

instance Pretty e => Pretty (LHS e) where
  ppPrec _ lhs =
    case lhs of
      LVar x      -> pp x
      LSelect l s -> pp l <> pp s

--------------------------------------------------------------------------------


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
        where doc = pp op <+> ppPrec p e
              p   = case op of
                      Not      -> 7
                      IntCast  -> 12
                      RealCast -> 12
                      Neg      -> 13
                      Pre      -> 13
                      Current  -> 13

      EOp2 e1 op e2 -> parenIf (n >= p) doc
        where doc = ppPrec lp e1 <+> pp op <+> ppPrec rp e2
              left x  = (x-1,x,x)
              right x = (x,x,x-1)
              non x   = (x,x,x)

              (lp,p,rp) = case op of
                            Concat  -> left 1
                            Fby     -> non 2
                            Implies -> right 3
                            Or      -> left 4
                            Xor     -> left 4
                            And     -> left 5
                            Lt      -> non 6
                            Leq     -> non 6
                            Gt      -> non 6
                            Geq     -> non 6
                            Eq      -> non 6
                            Neq     -> non 6
                            Add     -> left 8
                            Sub     -> left 8
                            Mul     -> left 9
                            Div     -> left 9
                            Mod     -> left 9
                            Power   -> left 10
                            Replicate -> left 14

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

-- | Pretty print a safety, but don't say anything if safe.
ppSafetyOpt :: Safety -> Doc
ppSafetyOpt saf =
  case saf of
    Safe -> empty
    Unsafe -> "unsafe"

instance Pretty Safety where
  ppPrec _ saf =
    case saf of
      Safe   -> "/* safe */"   -- so that it makes sense when printed
                               -- on its own
      Unsafe -> "unsafe"

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



