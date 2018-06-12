{
module Language.Lustre.Parser
  ( parse, parseStartingAt
  , program, expression
  ) where

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
  'nor'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwNor } }


  'current'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwCurrent } }
  'div'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwDiv } }
  'mod'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwMod } }
  'not'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwNot } }
  'or'        { Lexeme { lexemeRange = $$, lexemeToken = TokKwOr } }
  'pre'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwPre } }
  'when'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWhen } }
  'xor'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwXor } }
  'int'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwInt } }
  'real'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwReal } }
  'step'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwStep } }

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

%name program program
%name expression expression

%lexer { happyGetToken } { Lexeme { lexemeToken = TokEOF } }
%monad { Parser }

%nonassoc 'else'
%nonassoc '->'
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
  | name                          { Var $1   }
  | 'not' expression              { undefined }
  | '-' expression %prec UMINUS   { undefined }
  | 'pre' expression              { undefined }
  | 'current' expression          { undefined }
  | 'int' expression              { undefined }
  | 'real' expression             { undefined }
  | expression 'when' clock_expr  { undefined }
  {- expression 'fby' expression { undefined } -- what precedence?? -}
  | expression '->' expression  { undefined }
  | expression 'and' expression  { undefined }
  | expression 'or' expression  { undefined }
  | expression 'xor' expression  { undefined }
  | expression '=>' expression  { undefined }
  | expression '=' expression  { undefined }
  | expression '<>' expression  { undefined }
  | expression '<' expression  { undefined }
  | expression '<=' expression  { undefined }
  | expression '>' expression  { undefined }
  | expression '>=' expression  { undefined }
  | expression 'div' expression  { undefined }
  | expression '%' expression  { undefined }  -- This one is missing from gram?
  | expression 'mod' expression  { undefined }
  | expression '-' expression  { undefined }
  | expression '+' expression  { undefined }
  | expression '/' expression  { undefined }
  | expression '*' expression  { undefined }
  | 'if' expression 'then' expression 'else' expression { undefined }
  | 'with' expression 'then' expression 'else' expression { undefined }
  | '#' '(' expr_list ')'       { undefined }
  | 'nor' '(' expr_list ')'     { undefined }
  | effective_node '(' expr_list ')'  { undefined }
  | '[' expr_list ']'                 { undefined }
{-  | expression '^' expression         { undefined } Prec? -}
{-  | expression '|' expression         { undefined } Prec? -}
{-   | expression '[' expression ']'     { undefined } Prec? -}
{-  | expression '[' expression '..' expression Opt(step) ']' { undefined } -}
{-  | expression '.' ident       { undefined } -}


step :: { Expression }
  : 'step' expression             { $2 }

clock_expr :: { () }
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
  case lexemeToken l of
    TokInt n  -> Int n
    TokReal n -> Real n
    _         -> panic "toLit" [ "Unexcpected literal", show l ]


}
