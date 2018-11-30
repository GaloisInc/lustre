{-# Language OverloadedStrings #-}
module Language.Lustre.Pretty where

import Data.Semigroup ( (<>) )
import Data.Text (Text)
import Data.List(intersperse)
import qualified Data.Text as Text
import Text.PrettyPrint hiding ( (<>) )
import qualified Text.PrettyPrint as PP
import Numeric(showGFloat)
import Data.Ratio(numerator,denominator)

import Language.Lustre.AST
import AlexTools(prettySourceRange)

class Pretty t where
  ppPrec :: Int -> t -> Doc

-- | Pretty print with precedence 0.
pp :: Pretty t => t -> Doc
pp = ppPrec 0

-- | Pretty print with precedence 0, then convert to a 'String'.
showPP :: Pretty t => t -> String
showPP = show . pp

-- | Join vertically, with a space between each element.
vcatSep :: [Doc] -> Doc
vcatSep = vcat . intersperse " "

commaSep :: [Doc] -> Doc
commaSep = hsep . punctuate comma

instance Pretty Text where
  ppPrec _ = text . Text.unpack

instance Pretty SourceRange where
  ppPrec _ = text . prettySourceRange

instance Pretty Ident where
  ppPrec n i = ppPrec n (identText i)

instance Pretty Name where
  ppPrec n nam =
    case nam of
      Unqual i   -> ppPrec n i
      Qual _ x y -> ppPrec n x PP.<> "::" PP.<> ppPrec n y

--------------------------------------------------------------------------------

instance Pretty Integer where
  ppPrec _ = integer

instance Pretty Int where
  ppPrec _ x = text (show x)

instance Pretty TopDecl where
  ppPrec n td =
    case td of
      DeclareType dt      -> ppPrec n dt
      DeclareConst cd     -> ppPrec n cd <> semi
      DeclareNode nd      -> ppPrec n nd
      DeclareNodeInst nid -> ppPrec n nid
      DeclareContract cd  -> ppPrec n cd

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

instance Pretty InputBinder where
  ppPrec n ib =
    case ib of
      InputBinder b  -> ppPrec n b
      InputConst i t -> "const" <+> pp i <+> ":" <+> pp t

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
      Assert _ e -> "assert" <+> pp e
      Define ls e -> hsep (punctuate comma (map pp ls)) <+> "=" <+> pp e
      IsMain _ -> "--%MAIN"
      IVC is   -> "--%IVC" <+> hsep (punctuate comma (map pp is))
      Property _ e -> "--%PROPERTY" <+> pp e

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
      NamedType x       -> pp x
      ArrayType t e     -> pp t <+> "^" <+> pp e      -- precedence?
      IntType           -> "int"
      RealType          -> "real"
      BoolType          -> "bool"
      IntSubrange e1 e2 ->
        "subrange" <+> brackets (hsep (punctuate comma (map pp [e1,e2])))
                   <+> "of" <+> "int"
      TVar x            -> ppPrec n x
      TypeRange _ t     -> ppPrec n t

instance Pretty TVar where
  ppPrec _ (TV n) = "tv_" PP.<> int n


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
15   %right     'fby'
16   %right    '['
-}
instance Pretty Expression where
  ppPrec n expr =
    case expr of
      ERange _ e    -> ppPrec n e
      Var x         -> pp x
      Lit l         -> pp l
      e `When` ce   -> parenIf (n > 10) doc
        where doc = ppPrec 11 e <+> "when" <+> ppPrec 11 ce


      Tuple es      -> parens (hsep (punctuate comma (map pp es)))
      Array es      -> brackets (hsep (punctuate comma (map pp es)))
      Select e s    -> ppPrec 13 e <> pp s
      Struct s mb fs ->
        pp s <+> braces (mbWith <+> vcat (punctuate semi (map pp fs)))
          where mbWith = case mb of
                           Nothing -> mempty
                           Just x  -> pp x <+> "with"


      WithThenElse e1 e2 e3 -> parenIf (n > 0) doc
        where doc = "with" <+> pp e1 $$ nest 2 ("then" <+> ppPrec 0 e2)
                                     $$ nest 2 ("else" <+> ppPrec 0 e3)

      Merge i as  -> parenIf (n > 1) doc
        where doc = "merge" <+> pp i $$ nest 2 (vcat (map pp as))

      Call f es ->
        case f of
          NodeInst (CallPrim _ prim) [] ->
            case (prim, es) of

              (Op1 op, [e]) -> parenIf (n >= p) doc
                where doc = pp op <+> ppPrec p e
                      p   = case op of
                              Not      -> 7
                              IntCast  -> 12
                              RealCast -> 12
                              Neg      -> 13
                              Pre      -> 13
                              Current  -> 13

              (Op2 op, [e1,e2]) -> parenIf (n >= p) doc
                 where doc = ppPrec lp e1 <+> pp op <+> ppPrec rp e2
                       left x  = (x-1,x,x)
                       right x = (x,x,x-1)
                       non x   = (x,x,x)

                       (lp,p,rp) = case op of
                                     Concat  -> left 1
                                     FbyArr  -> non 2
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
                                     Fby     -> right 15

              (ITE,[e1,e2,e3]) -> parenIf (n > 0) doc
                where doc = "if" <+> pp e1 $$ nest 2 ("then" <+> ppPrec 0 e2)
                                           $$ nest 2 ("else" <+> ppPrec 0 e3)

              _ -> pp f <+> parens (hsep (punctuate comma (map pp es)))

          _ -> pp f <+> parens (hsep (punctuate comma (map pp es)))

parenIf :: Bool -> Doc -> Doc
parenIf p d = if p then parens d else d


instance Pretty e => Pretty (MergeCase e) where
  ppPrec _ (MergeCase cv e) = parens (pp cv <+> "->" <+> pp e)

instance Pretty e => Pretty (Field e) where
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
      Lit (Bool True)  -> pp i
      Lit (Bool False) -> "not" <+> pp i
      _                -> ppPrec 16 cv <> parens (pp i)

instance Pretty NodeInst where
  ppPrec _ (NodeInst x as) =
    case as of
      [] -> pp x
      _  -> pp x <+> "<<" PP.<> hsep (punctuate comma (map pp as)) PP.<> ">>"

instance Pretty Callable where
  ppPrec p c =
    case c of
      CallUser n   -> ppPrec p n
      CallPrim _ i -> ppPrec p i

instance Pretty PrimNode where
  ppPrec p x =
    case x of
      Iter i -> ppPrec p i
      Op1 op -> ppPrec p op
      Op2 op -> ppPrec p op
      OpN op -> ppPrec p op
      ITE    -> "if"

instance Pretty Iter where
  ppPrec _ i =
    case i of
      IterFill    -> "fill"
      IterRed     -> "red"
      IterFillRed -> "fillred"
      IterMap     -> "map"
      IterBoolRed -> "boolred"

instance Pretty StaticArg where
  ppPrec n arg =
    case arg of
      TypeArg t     -> "type" <+> pp t
      ExprArg e     -> "const" <+> pp e
      NodeArg nf x  -> case x of
                         NodeInst (CallUser _) _ -> pp nf <+> pp x
                         _ -> pp x
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
      FbyArr      -> "->"
      Fby         -> "fby"
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

--------------------------------------------------------------------------------

instance Pretty Contract where
  ppPrec _ c = "/*@contract" $$ nest 2 (vcat (map pp (contractItems c))) $$ "*/"

instance Pretty ContractItem where
  ppPrec _ item =
    case item of
      GhostConst x mbT e -> "const" <+> pp x <+> sig <+> "=" <+> pp e PP.<> semi
        where sig = maybe empty (\t -> ":" <+> pp t) mbT
      GhostVar b e -> "var" <+> pp b <+> "=" <+> pp e PP.<> semi
      Assume e -> "assume" <+> pp e PP.<> semi
      Guarantee e -> "guarantee" <+> pp e PP.<> semi
      Mode i res ens -> "mode" <+> pp i <+> "("
                        $$ nest 2 (vcat (map (ppClause "requre") res))
                        $$ nest 2 (vcat (map (ppClause "ensure") ens))
                        $$ ")" PP.<> semi
        where ppClause x e = x <+> pp e PP.<> semi
      Import i eis eos ->
        "import" <+> pp i PP.<> parens (commaSep (map pp eis))
                            <+> parens (commaSep (map pp eos))

instance Pretty ContractDecl where
  ppPrec _ cd =
    "contract" <+> pp (cdName cd) <+> pp (cdProfile cd) PP.<> semi
    $$ "let" $$ nest 2 (vcat (map pp (cdItems cd))) $$ "tel"


