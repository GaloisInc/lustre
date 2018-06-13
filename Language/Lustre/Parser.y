{
module Language.Lustre.Parser
  ( parse, parseStartingAt
  , program, expression
  ) where

import AlexTools(HasRange, (<->))

import Language.Lustre.Parser.Lexer
import Language.Lustre.Parser.Monad
import Language.Lustre.AST
import Language.Lustre.Panic
}


%tokentype { Lexeme Token }

%token

  'if'        { Lexeme { lexemeRange = $$, lexemeToken = TokKwIf } }
  'then'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwThen } }
  'else'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwElse } }
  'with'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWith } }

  'and'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwAnd } }
  'not'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwNot } }
  'or'        { Lexeme { lexemeRange = $$, lexemeToken = TokKwOr } }
  'xor'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwXor } }
  'nor'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwNor } }
  '=>'        { Lexeme { lexemeRange = $$, lexemeToken = TokImplies } }
  '<'         { Lexeme { lexemeRange = $$, lexemeToken = TokLt } }
  '<='        { Lexeme { lexemeRange = $$, lexemeToken = TokLeq } }
  '='         { Lexeme { lexemeRange = $$, lexemeToken = TokEq } }
  '>='        { Lexeme { lexemeRange = $$, lexemeToken = TokGeq } }
  '>'         { Lexeme { lexemeRange = $$, lexemeToken = TokGt } }
  '<>'        { Lexeme { lexemeRange = $$, lexemeToken = TokNotEq } }

  'extern'    { Lexeme { lexemeRange = $$, lexemeToken = TokKwExtern } }
  'unsafe'    { Lexeme { lexemeRange = $$, lexemeToken = TokKwUnsafe } }
  'node'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwNode } }
  'function'  { Lexeme { lexemeRange = $$, lexemeToken = TokKwFunction } }
  'returns'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwReturns } }

  'type'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwType } }
  'const'     { Lexeme { lexemeRange = $$, lexemeToken = TokKwConst } }


  'when'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWhen } }
  'current'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwCurrent } }
  'pre'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwPre } }
  'fby'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwFby } }

  'div'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwDiv } }
  'mod'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwMod } }
  'step'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwStep } }
  '->'        { Lexeme { lexemeRange = $$, lexemeToken = TokRightArrow } }

  'int'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwInt } }
  'real'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwReal } }
  'bool'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwBool } }


  ':'         { Lexeme { lexemeRange = $$, lexemeToken = TokColon } }
  '::'        { Lexeme { lexemeRange = $$, lexemeToken = TokColonColon } }
  ','         { Lexeme { lexemeRange = $$, lexemeToken = TokComma } }
  ';'         { Lexeme { lexemeRange = $$, lexemeToken = TokSemi } }
  '.'         { Lexeme { lexemeRange = $$, lexemeToken = TokDot } }
  '..'        { Lexeme { lexemeRange = $$, lexemeToken = TokDotDot } }


  '('         { Lexeme { lexemeRange = $$, lexemeToken = TokOpenParen } }
  ')'         { Lexeme { lexemeRange = $$, lexemeToken = TokCloseParen } }
  '<<'        { Lexeme { lexemeRange = $$, lexemeToken = TokOpenTT } }
  '>>'        { Lexeme { lexemeRange = $$, lexemeToken = TokCloseTT } }
  '['         { Lexeme { lexemeRange = $$, lexemeToken = TokOpenBracket } }
  ']'         { Lexeme { lexemeRange = $$, lexemeToken = TokCloseBracket } }
  '{'         { Lexeme { lexemeRange = $$, lexemeToken = TokOpenBrace } }
  '}'         { Lexeme { lexemeRange = $$, lexemeToken = TokCloseBrace } }

  '+'         { Lexeme { lexemeRange = $$, lexemeToken = TokPlus } }
  '-'         { Lexeme { lexemeRange = $$, lexemeToken = TokMinus } }
  '*'         { Lexeme { lexemeRange = $$, lexemeToken = TokTimes } }
  '/'         { Lexeme { lexemeRange = $$, lexemeToken = TokDiv } }
  '#'         { Lexeme { lexemeRange = $$, lexemeToken = TokHash } }
  '|'         { Lexeme { lexemeRange = $$, lexemeToken = TokBar } }
  '^'         { Lexeme { lexemeRange = $$, lexemeToken = TokHat } }

  '%'         { Lexeme { lexemeRange = $$, lexemeToken = TokMod } }

  IDENT       { $$@Lexeme { lexemeToken = TokIdent {} } }
  INT         { $$@Lexeme { lexemeToken = TokInt   {} } }
  REAL        { $$@Lexeme { lexemeToken = TokReal  {} } }
  BOOL        { $$@Lexeme { lexemeToken = TokBool  {} } }

%name program program
%name expression expression

%lexer { happyGetToken } { Lexeme { lexemeToken = TokEOF } }
%monad { Parser }

%left     'else'
%left     '|'
%nonassoc 'step'
%nonassoc '..'
%nonassoc '->'
%right    '=>'
%nonassoc 'or' 'xor'
%nonassoc 'and'
%nonassoc '<' '<=' '=' '>=' '>' '<>'
%nonassoc 'not'
%left     '+' '-'
%left     '*' '/' '%' 'mod' 'div'
%nonassoc 'when'
%nonassoc 'int' 'real'
%nonassoc UMINUS 'pre' 'current'
%left     '^' '.'
%right    '[' '{' ';'
%right    ','
%right 'fby'


%%

program :: { [TopDecl] }
  : const_block { undefined}

const_block :: { [TopDecl] }
  : 'const' EndBy1(';',const_def_decl)    { $2 }

{-
type_block :: [TopDecl]
  : 'type' EndBy1(';',type_def_decl)      { $2 }

type_def_decl :: { TopDecl }
  : type_decl                         { 
-}

{- XXX: Pragmas -}
const_def_decl :: { TopDecl }
  : const_decl                        { DeclareConst (fst $1) (snd $1) [] }
  | const_def_head '=' expression     { toConstDef $1 $3 }

const_def_head :: { (Ident, Maybe Type) }
  : ident                             { ($1, Nothing) }
  | const_decl                        {% toConstDefHead $1 }

const_decl :: { ([Ident], Type) }
  : SepBy1(',',ident) ':' type        { ($1,$3) }

type :: { Type }
  : baseType                          { $1 }
  | type '^' expression               { at $1 $3 (ArrayType $1 $3) }

baseType :: { Type }
  : 'int'                             { at $1 $1 IntType       }
  | 'real'                            { at $1 $1 RealType      }
  | 'bool'                            { at $1 $1 BoolType      }
  | name                              { NamedType $1           }

expression :: { Expression }
  : INT                               { toLit $1 }
  | REAL                              { toLit $1 }
  | BOOL                              { toLit $1 }

  | name                              { Var $1   }

  | 'not'     expression              { toE1 Not      $1 $2 }
  | '-'       expression %prec UMINUS { toE1 Neg      $1 $2 }
  | 'pre'     expression              { toE1 Pre      $1 $2 }
  | 'current' expression              { toE1 Current  $1 $2 }
  | 'int'     expression              { toE1 IntCast  $1 $2 }
  | 'real'    expression              { toE1 RealCast $1 $2 }

  | expression 'when' expression      { EOp2 $1 When     $3 } -- XXX: clock
  | expression 'fby' expression       { EOp2 $1 Fby      $3 }
  | expression '->' expression        { EOp2 $1 Fby      $3 }
  | expression 'and' expression       { EOp2 $1 And      $3 }
  | expression 'or' expression        { EOp2 $1 Or       $3 }
  | expression 'xor' expression       { EOp2 $1 Xor      $3 }
  | expression '=>' expression        { EOp2 $1 Implies  $3 }
  | expression '=' expression         { EOp2 $1 Eq       $3 }
  | expression '<>' expression        { EOp2 $1 Neq      $3 }
  | expression '<' expression         { EOp2 $1 Lt       $3 }
  | expression '<=' expression        { EOp2 $1 Leq      $3 }
  | expression '>' expression         { EOp2 $1 Gt       $3 }
  | expression '>=' expression        { EOp2 $1 Geq      $3 }
  | expression 'div' expression       { EOp2 $1 IntDiv   $3 }
  | expression 'mod' expression       { EOp2 $1 Mod      $3 }
  | expression '-' expression         { EOp2 $1 Sub      $3 }
  | expression '+' expression         { EOp2 $1 Add      $3 }
  | expression '/' expression         { EOp2 $1 Div      $3 }
  | expression '*' expression         { EOp2 $1 Mul      $3 }

  | expression '^' expression         { EOp2 $1 Replicate $3 }
  | expression '|' expression         { EOp2 $1 Concat    $3 }

  | 'if' expression
      'then' expression
      'else' expression               { at $1 $6 (IfThenElse $2 $4 $6) }

  | 'with' expression
      'then' expression
      'else' expression               { at $1 $6 (WithThenElse $2 $4 $6) }

  | '#' '(' expr_list ')'             { at $1 $4 (EOpN AtMostOne $3) }
  | 'nor' '(' expr_list ')'           { at $1 $4 (EOpN Nor $3) }

  | '[' expr_list ']'                 { at $1 $3 (Array $2) }

  | expression '[' arraySel ']'       { at $1 $4 (Select $1 $3) }
  | expression '.' ident              { at $1 $3 (Select $1 (SelectField $3))}

  | name '(' expr_list ')'            { at $1 $4 (CallPos (NodeName $1 []) $3) }

arraySel :: { Selector }
  : expression                        { SelectElement $1 }
  | arraySlice                        { SelectSlice $1 }

arraySlice :: { ArraySlice }
  : expression '..' expression Opt(step) { ArraySlice $1 $3 $4 }

step :: { Expression }
  : 'step' expression                 { $2 }



named_call_params :: { [()] }
  : SepBy1(arg_sep, named_call_param) { $1 }

arg_sep :: { SourceRange }
  : ';'           { $1 }
  | ','           { $1 }

named_call_param :: { () }
  : ident '=' expression      { undefined }

expr_list :: { [Expression] }
  : SepBy1(',',expression)          { $1 } 

name :: { Name }
  : ident                 { Unqual $1 }
  | ident '::' ident      { Qual $1 $3 }

ident :: { Ident }
  : IDENT                 { toIdent $1 }


{- EBNF combinators -}

{- Both should have the same type -}

Opt(x) :: { Maybe x }
  : {- nothing -}       { Nothing }
  | x                   { Just $1 }

SepBy1(sep,thing) :: { [thing] }
  : SepBy1_rev(sep,thing) { reverse $1 }

SepBy1_rev(sep,thing) :: { [thing] }
  : thing                           { [$1] }
  | SepBy1_rev(sep,thing) sep thing { $3 : $1 }


EndBy1(sep,thing) :: { [thing] }
  : EndBy1_rev(sep,thing) { reverse $1 }

EndBy1_rev(sep,thing) :: { [thing] }
  : thing sep                       { [$1] }
  | EndBy1_rev(sep,thing) thing sep { $2 : $1 }





{

toIdent :: Lexeme Token -> Ident
toIdent l = Ident { identText  = lexemeText l
                  , identRange = lexemeRange l
                  }

toLit :: Lexeme Token -> Expression
toLit l =
  ERange (lexemeRange l) $
  Lit $
  case lexemeToken l of
    TokInt n    -> Int n
    TokReal n   -> Real n
    TokBool n   -> Bool n
    _           -> panic "toLit" [ "Unexcpected literal", show l ]

class At t where
  at :: (HasRange a, HasRange b) => a -> b -> t -> t

instance At Expression where
  at x y = ERange (x <-> y)

instance At Type where
  at x y = TypeRange (x <-> y)

toE1 :: Op1 -> SourceRange -> Expression -> Expression
toE1 op rng expr = at rng expr (EOp1 op expr)

toE2 :: Op2 -> Expression -> Expression -> Expression
toE2 op e1 e2 = EOp2 e1 op e2

toConstDefHead :: ([Ident],Type) -> Parser (Ident,Maybe Type)
toConstDefHead (is,t) =
  case is of
    [i] -> return (i,Just t)
    _   -> parseError (MultipleNamesInConstantDefintion is)

toConstDef :: (Ident,Maybe Type) -> Expression -> TopDecl
toConstDef (i,t) e = DefineConst (ConstDef i t e [])
}
