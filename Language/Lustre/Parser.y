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


  'current'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwCurrent } }
  'div'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwDiv } }
  'mod'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwMod } }
  'pre'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwPre } }
  'when'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWhen } }
  'int'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwInt } }
  'real'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwReal } }
  'step'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwStep } }
  'fby'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwFby } }


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

  '->'        { Lexeme { lexemeRange = $$, lexemeToken = TokRightArrow } }
  '=>'        { Lexeme { lexemeRange = $$, lexemeToken = TokFatRightArrow } }
  '<'         { Lexeme { lexemeRange = $$, lexemeToken = TokLt } }
  '<='        { Lexeme { lexemeRange = $$, lexemeToken = TokLeq } }
  '='         { Lexeme { lexemeRange = $$, lexemeToken = TokEq } }
  '>='        { Lexeme { lexemeRange = $$, lexemeToken = TokGeq } }
  '>'         { Lexeme { lexemeRange = $$, lexemeToken = TokGt } }
  '<>'        { Lexeme { lexemeRange = $$, lexemeToken = TokNotEq } }
  '+'         { Lexeme { lexemeRange = $$, lexemeToken = TokPlus } }
  '-'         { Lexeme { lexemeRange = $$, lexemeToken = TokMinus } }
  '*'         { Lexeme { lexemeRange = $$, lexemeToken = TokTimes } }
  '/'         { Lexeme { lexemeRange = $$, lexemeToken = TokDiv } }
  '%'         { Lexeme { lexemeRange = $$, lexemeToken = TokMod } }
  '#'         { Lexeme { lexemeRange = $$, lexemeToken = TokHash } }
  '|'         { Lexeme { lexemeRange = $$, lexemeToken = TokBar } }
  '^'         { Lexeme { lexemeRange = $$, lexemeToken = TokHat } }

  IDENT       { $$@Lexeme { lexemeToken = TokIdent {} } }
  INT         { $$@Lexeme { lexemeToken = TokInt   {} } }
  REAL        { $$@Lexeme { lexemeToken = TokReal  {} } }
  BOOL        { $$@Lexeme { lexemeToken = TokBool  {} } }

%name program program
%name expression expression

%lexer { happyGetToken } { Lexeme { lexemeToken = TokEOF } }
%monad { Parser }

%nonassoc 'else'
%nonassoc '->' 'fby'
%right    '=>'
%nonassoc 'or' 'xor'
%nonassoc 'and'
%nonassoc '<' '<=' '=' '>=' '>' '<>'
%nonassoc 'not'
%left     '+' '-'
%left     '*' '/' '%' 'mod' 'div'
%nonassoc 'when'
%nonassoc UMINUS 'pre' 'current' 'int' 'real'


%%

program :: { () }
  : INT { () }

expression :: { Expression }
  : INT                           { toLit $1 }
  | REAL                          { toLit $1 }
  | BOOL                          { toLit $1 }

  | name                              { Var $1   }

  | 'not'     expression              { toE1 Not      $1 $2 }
  | '-'       expression %prec UMINUS { toE1 Neg      $1 $2 }
  | 'pre'     expression              { toE1 Pre      $1 $2 }
  | 'current' expression              { toE1 Current  $1 $2 }
  | 'int'     expression              { toE1 IntCast  $1 $2 }
  | 'real'    expression              { toE1 RealCast $1 $2 }

  | expression 'when' clock_expr      { EOp2 $1 When     $3 } -- XXX: clock
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

  | 'if' expression
      'then' expression
      'else' expression      { ERange ($1 <-> $6) (IfThenElse $2 $4 $6) }

  | 'with' expression
      'then' expression
      'else' expression      { ERange ($1 <-> $6) (WithThenElse $2 $4 $6) }

  | '#' '(' expr_list ')'       { at $1 $4 (EOpN AtMostOne $3) }
  | 'nor' '(' expr_list ')'     { at $1 $4 (EOpN Nor $3) }

  | effective_node '(' expr_list ')'  { undefined }
  | '[' expr_list ']'                 { undefined }

{-  | expression '^' expression         { undefined } Prec? -}
{-  | expression '|' expression         { undefined } Prec? -}
{-   | expression '[' expression ']'     { undefined } Prec? -}
{-  | expression '[' expression '..' expression Opt(step) ']' { undefined } -}
{-  | expression '.' ident       { undefined } -}


step :: { Expression }
  : 'step' expression             { $2 }

clock_expr :: { Expression }
  : name '(' ident ')'            { undefined }
  | ident                         { undefined }
  | 'not' ident                   { undefined }
  | 'not' '(' ident ')'           { undefined }

effective_node :: { () }
  : name                            { undefined }
  {- XXX  | name '<<' static_arg_list '>>'  { undefined } -}


named_call_params :: { [()] }
  : SepBy1(named_call_sep, named_call_param) { $1 }

named_call_sep :: { () }
  : ';'           { () }
  | ','           { () }

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


at :: (HasRange a, HasRange b) => a -> b -> Expression -> Expression
at x y = ERange (x <-> y)

toE1 :: Op1 -> SourceRange -> Expression -> Expression
toE1 op rng expr = at rng expr (EOp1 op expr)

toE2 :: Op2 -> Expression -> Expression -> Expression
toE2 op e1 e2 = EOp2 e1 op e2


}
