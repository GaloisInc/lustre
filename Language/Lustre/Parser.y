{
{-# Language OverloadedStrings #-}
module Language.Lustre.Parser
  ( parse, parseStartingAt
  , parseProgramFrom
  , parseProgramFromFileUTF8
  , parseProgramFromFileLatin1
  , program, expression
  , ParseError(..)
  , prettySourcePos, prettySourcePosLong
  , prettySourceRange, prettySourcePosLong
  ) where

import AlexTools
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Text.Encoding as Text
import qualified Data.ByteString as BS
import Control.Exception(throwIO)

import Language.Lustre.Parser.Lexer
import Language.Lustre.Parser.Monad
import Language.Lustre.AST
import Language.Lustre.Panic
}


%tokentype { Lexeme Token }

%token

  'package'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwPackage } }
  'model'     { Lexeme { lexemeRange = $$, lexemeToken = TokKwModel } }
  'is'        { Lexeme { lexemeRange = $$, lexemeToken = TokKwIs } }
  'uses'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwUses } }
  'needs'     { Lexeme { lexemeRange = $$, lexemeToken = TokKwNeeds } }
  'provides'  { Lexeme { lexemeRange = $$, lexemeToken = TokKwProvides } }
  'body'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwBody } }
  'end'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwEnd } }

  'if'        { Lexeme { lexemeRange = $$, lexemeToken = TokKwIf } }
  'then'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwThen } }
  'else'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwElse } }
  'with'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWith } }
  'merge'     { Lexeme { lexemeRange = $$, lexemeToken = TokKwMerge } }

  'and'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwAnd } }
  'not'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwNot } }
  'or'        { Lexeme { lexemeRange = $$, lexemeToken = TokKwOr } }
  'xor'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwXor } }
  'nor'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwNor } }
  '#'         { Lexeme { lexemeRange = $$, lexemeToken = TokHash } }
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
  'var'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwVar } }
  'struct'    { Lexeme { lexemeRange = $$, lexemeToken = TokKwStruct } }
  'enum'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwEnum } }
  'assert'    { Lexeme { lexemeRange = $$, lexemeToken = TokKwAssert } }
  '--%PROPERTY' { Lexeme { lexemeRange = $$, lexemeToken = TokPragmaProperty } }
  '--%MAIN'     { Lexeme { lexemeRange = $$, lexemeToken = TokPragmaMain } }

  'when'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWhen } }
  'current'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwCurrent } }
  'pre'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwPre } }
  'fby'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwFby } }
  '->'        { Lexeme { lexemeRange = $$, lexemeToken = TokRightArrow } }

  'div'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwDiv } }
  'mod'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwMod } }
  '+'         { Lexeme { lexemeRange = $$, lexemeToken = TokPlus } }
  '-'         { Lexeme { lexemeRange = $$, lexemeToken = TokMinus } }
  '*'         { Lexeme { lexemeRange = $$, lexemeToken = TokStar } }
  '**'        { Lexeme { lexemeRange = $$, lexemeToken = TokStarStar } }
  '/'         { Lexeme { lexemeRange = $$, lexemeToken = TokDiv } }


  'step'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwStep } }
  '|'         { Lexeme { lexemeRange = $$, lexemeToken = TokBar } }
  '^'         { Lexeme { lexemeRange = $$, lexemeToken = TokHat } }
  '..'        { Lexeme { lexemeRange = $$, lexemeToken = TokDotDot } }

  'int'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwInt } }
  'real'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwReal } }
  'bool'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwBool } }


  ':'         { Lexeme { lexemeRange = $$, lexemeToken = TokColon } }
  ','         { Lexeme { lexemeRange = $$, lexemeToken = TokComma } }
  ';'         { Lexeme { lexemeRange = $$, lexemeToken = TokSemi } }
  '.'         { Lexeme { lexemeRange = $$, lexemeToken = TokDot } }


  'let'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwLet } }
  'tel'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwTel } }
  '('         { Lexeme { lexemeRange = $$, lexemeToken = TokOpenParen } }
  ')'         { Lexeme { lexemeRange = $$, lexemeToken = TokCloseParen } }
  '<<'        { Lexeme { lexemeRange = $$, lexemeToken = TokOpenTT } }
  '>>'        { Lexeme { lexemeRange = $$, lexemeToken = TokCloseTT } }
  '['         { Lexeme { lexemeRange = $$, lexemeToken = TokOpenBracket } }
  ']'         { Lexeme { lexemeRange = $$, lexemeToken = TokCloseBracket } }
  '{'         { Lexeme { lexemeRange = $$, lexemeToken = TokOpenBrace } }
  '}'         { Lexeme { lexemeRange = $$, lexemeToken = TokCloseBrace } }

  '%'         { Lexeme { lexemeRange = $$, lexemeToken = TokMod } }


  IDENT       { $$@Lexeme { lexemeToken = TokIdent {} } }
  QIDENT      { $$@Lexeme { lexemeToken = TokQualIdent {} } }
  INT         { $$@Lexeme { lexemeToken = TokInt   {} } }
  REAL        { $$@Lexeme { lexemeToken = TokReal  {} } }
  BOOL        { $$@Lexeme { lexemeToken = TokBool  {} } }

%name program program
%name package packDecl
%name model   modelDecl
%name expression expression

%lexer { happyGetToken } { Lexeme { lexemeToken = TokEOF } }
%monad { Parser }

%left     'else'
%left     '|'
%nonassoc '->'
%right    '=>'
%left     'or' 'xor'
%left     'and'
%nonassoc '<' '<=' '=' '>=' '>' '<>'
%nonassoc 'not'
%left     '+' '-'
%left     '*' '/' '%' 'mod' 'div'
%left     '**'
%nonassoc 'when'
%nonassoc 'int' 'real'
%nonassoc UMINUS 'pre' 'current'
%left     '^' '.'
%right    '['
%right    'fby'


%%

program :: { Program }
  : packBody          { ProgramDecls $1 }
  | ListOf1(packTop)  { ProgramPacks $1 }

packTop :: { PackDecl }
  : packDecl          { PackDecl $1 }
  | modelDecl         { PackDecl $1 }
  | 'package' ident eq_is ident '(' SepBy1(staticArgSep,staticNamedArg) ')' ';'
                      { PackInst $2 $4 $6 }


eq_is :: { SourceRange }
  : '='               { $1 }
  | 'is'              { $1 }


-- Packages --------------------------------------------------------------------

packDecl
  : 'package' ident packUses packProvides 'body' packBody 'end'
  { Package { packageName     = $2
            , packageUses     = $3
            , packageParams   = []
            , packageProvides = $4
            , packageBody     = $6
            , packageRange    = $1 <-> $7
            }
  }

packUses :: { [Ident] }
  : 'uses' SepBy1(',',ident) ';'            { $2 }
  | {- empty -}                             { [] }

packProvides :: { [PackageProvides] }
  : 'provides' EndBy1(';',packProvide)      { $2 }
  | {- empty -}                             { [] }

packProvide :: { PackageProvides }
  : 'const' ident ':' type Opt(provideDef)   { ProvidesConst $2 $4 $5 }
  | 'type' typeDecl                          { ProvidesType $2 }
  | Perhaps('unsafe') nodeType ident staticParams nodeProfile
      { ProvidesNode
        NodeDecl { nodeExtern       = False
                 , nodeSafety       = isUnsafe $1
                 , nodeType         = $2
                 , nodeName         = $3
                 , nodeStaticInputs = $4
                 , nodeProfile      = $5
                 , nodeDef          = Nothing
                 } }

provideDef :: { Expression }
  : '=' expression                      { $2 }


packBody :: { [TopDecl] }
  : ListOf1(topDecl) { concat $1 }


-- Models ----------------------------------------------------------------------

modelDecl :: { Package }
  : 'model' ident packUses 'needs' EndBy1(';',staticParam) packProvides
    'body' packBody 'end'
  { Package { packageName     = $2
            , packageUses     = $3
            , packageParams   = $5
            , packageProvides = $6
            , packageBody     = $8
            , packageRange    = $1 <-> $9
            }
  }




--------------------------------------------------------------------------------

topDecl :: { [TopDecl] }
  : 'const' EndBy1(';',constDef)     { map DeclareConst (concat $2) }
  | 'type' EndBy1(';',typeDecl)      { map DeclareType  $2 }
  | extDecl                          { [ DeclareNode $1 ] }
  | nodeDecl                         { [ DeclareNode $1 ] }
  | nodeInstDecl                     { [ DeclareNodeInst $1 ] }


-- Constant Declarations -------------------------------------------------------

constDef :: { [ConstDef] }
  : ident ':' type                        { toConstDef ($1,$3) }
  | ident ',' SepBy1(',',ident) ':' type  { toConstDef ($1,$3,$5) }
  | ident '=' expression                  { toConstDef ($1,$3) }
  | ident ':' type '=' expression         { toConstDef ($1,$3,$5) }


-- Type Declarations -----------------------------------------------------------

typeDecl :: { TypeDecl }
  : ident                                     { toTypeDecl $1 Nothing }
  | ident '=' typeDef                         { toTypeDecl $1 (Just $3) }

typeDef :: { TypeDef }
  : type                                               { IsType $1 }
  | 'enum' '{' SepBy1(',',ident) '}'                   { IsEnum $3 }
  | Perhaps('struct') '{' SepEndBy1(';',fieldType) '}' { IsStruct (concat $3) }


fieldType :: { [FieldType] }
  : ident ':' type '=' expression             { toFieldType ($1,$3,$5) }
  | ident ':' type                            { toFieldType ($1,$3) }
  | ident ',' SepBy1(',',ident) ':' type      { toFieldType ($1, $3, $5) }


-- Types -----------------------------------------------------------------------

type :: { Type }
  : builtInType                               { $1 }
  | name                                      { NamedType $1 }
  | type '^' expression                       { at $1 $3 (ArrayType $1 $3) }
  -- jkind notation
  | type '[' expression ']'                   { at $1 $4 (ArrayType $1 $3) }

simpleType :: { Type }
  : builtInType                               { $1 }
  | simpleType '^' expression                 { at $1 $3 (ArrayType $1 $3) }

builtInType :: { Type }
  : 'int'                                     { at $1 $1 IntType       }
  | 'real'                                    { at $1 $1 RealType      }
  | 'bool'                                    { at $1 $1 BoolType      }




-- Node Declarations -----------------------------------------------------------

extDecl :: { NodeDecl }
  : Perhaps('unsafe') 'extern' nodeType ident nodeProfile Perhaps(';')
      { NodeDecl
          { nodeSafety  = isUnsafe $1
          , nodeExtern  = True
          , nodeType    = $3
          , nodeName    = $4
          , nodeStaticInputs = [] -- XXX
          , nodeProfile = $5
          , nodeDef     = Nothing
          }
      }

nodeDecl :: { NodeDecl }
  : Perhaps('unsafe') nodeType ident staticParams nodeProfile Perhaps(';')
    localDecls body Perhaps(';')
      { NodeDecl
          { nodeSafety  = isUnsafe $1
          , nodeExtern  = False
          , nodeType    = $2
          , nodeName    = $3
          , nodeStaticInputs = $4
          , nodeProfile = $5
          , nodeDef     = Just NodeBody { nodeLocals = $7, nodeEqns = $8 }
          }
      }

nodeInstDecl :: { NodeInstDecl }
  : Perhaps('unsafe') nodeType ident staticParams Opt(nodeProfile)
      '=' effNode Perhaps(';')
    { NodeInstDecl
        { nodeInstSafety        = isUnsafe $1
        , nodeInstType          = $2
        , nodeInstName          = $3
        , nodeInstStaticInputs  = $4
        , nodeInstProfile       = $5
        , nodeInstDef           = $7
        }
    }


nodeProfile :: { NodeProfile }
  : params 'returns' params { NodeProfile { nodeInputs = $1, nodeOutputs = $3 }}

nodeType :: { NodeType }
  : 'node'      { Node }
  | 'function'  { Function }

staticParams :: { [StaticParam] }
  : {- empty -}                       { [] }
  | '<<' SepBy1(';',staticParam) '>>' { $2 }

-- Description of a static parameter (i.e., this is the formal parameter)
staticParam :: { StaticParam }
  : 'type' ident                    { TypeParam $2 }
  | 'const' ident ':' type          { ConstParam $2 $4 }
  | Perhaps('unsafe')
    nodeType
    ident nodeProfile               { NodeParam (isUnsafe $1) $2 $3 $4 }

localDecls :: { [LocalDecl] }
  : {- empty -}                            { [] }
  | ListOf1(localDecl)                     { concat $1 }

localDecl :: { [LocalDecl] }
  : 'var' EndBy1(';',varDecl)              { map LocalVar (concat $2) }
  | 'const' EndBy1(';',constDef)           { map LocalConst (concat $2) }

body :: { [Equation] }
  : 'let' EndBy1(';',equation) 'tel'       { $2 }

equation :: { Equation }
  : 'assert' expression                    { Assert $2 }
  | '--%PROPERTY' expression               { Property $2 }
  | '--%MAIN'                              { IsMain }
  | SepBy1(',',LHS) '=' expression         { Define $1 $3 }
  | '(' SepBy1(',',LHS) ')' '=' expression { Define $2 $5 }

LHS :: { LHS Expression }
  : ident                                   { LVar $1 }
  | LHS '.' ident                           { LSelect $1 (SelectField $3) }
  | LHS '[' arraySel ']'                    { LSelect $1 $3 }


-- Variable Declarations -------------------------------------------------------

params :: { [Binder] }
  : '(' ')'                                 { [] }
  | '(' SepEndBy1(',',varDecl) ')'          { concat $2 }

varDecl :: { [Binder] }
  : typedIdents                             { toVarDeclBase $1 }
  | typedIdents 'when' clockExpr            { toVarDecl $1 $3  }
  | '(' typedIdents ')' 'when' clockExpr    { toVarDecl $2 $5  }

typedIdents :: { ( [Ident], Type ) }
  : SepBy1(',', ident) ':' type             { ($1, $3) }



-- Expressions -----------------------------------------------------------------

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

  | expression 'when' clockExpr       { $1 `When` $3        }
  | expression 'fby' expression       { toE2 $1 $2 Fby     $3 }
  | expression '->' expression        { toE2 $1 $2 FbyArr  $3 }
  | expression 'and' expression       { toE2 $1 $2 And     $3 }
  | expression 'or' expression        { toE2 $1 $2 Or      $3 }
  | expression 'xor' expression       { toE2 $1 $2 Xor     $3 }
  | expression '=>' expression        { toE2 $1 $2 Implies $3 }
  | expression '=' expression         { toE2 $1 $2 Eq      $3 }
  | expression '<>' expression        { toE2 $1 $2 Neq     $3 }
  | expression '<' expression         { toE2 $1 $2 Lt      $3 }
  | expression '<=' expression        { toE2 $1 $2 Leq     $3 }
  | expression '>' expression         { toE2 $1 $2 Gt      $3 }
  | expression '>=' expression        { toE2 $1 $2 Geq     $3 }
  | expression 'div' expression       { toE2 $1 $2 Div     $3 }
  | expression 'mod' expression       { toE2 $1 $2 Mod     $3 }
  | expression '-' expression         { toE2 $1 $2 Sub     $3 }
  | expression '+' expression         { toE2 $1 $2 Add     $3 }
  | expression '/' expression         { toE2 $1 $2 Div     $3 }
  | expression '*' expression         { toE2 $1 $2 Mul     $3 }
  | expression '**' expression        { toE2 $1 $2 Power   $3 }

  | expression '^' expression         { toE2 $1 $2 Replicate $3 }
  | expression '|' expression         { toE2 $1 $2 Concat    $3 }

  | 'if' expression
      'then' expression
      'else' expression               { toITE $1 $2 $4 $6 }

  | 'with' expression
      'then' expression
      'else' expression               { at $1 $6 (WithThenElse $2 $4 $6) }

  | 'merge' ident ListOf1(mergeCase)  { toMerge $1 $2 $3 }

  | '#' '(' exprList ')'              { toEN AtMostOne $1 $4 $3 }
  | 'nor' '(' exprList ')'            { toEN Nor $1 $4 $3 }

  | '[' exprList ']'                  { at $1 $3 (Array $2) }

  | expression '[' arraySel ']'       { at $1 $4 (Select $1 $3) }
  | expression '.' ident              { at $1 $3 (Select $1 (SelectField $3))}

  | effNode '(' exprList ')'          { at $1 $4 (CallPos $1 $3) }
  | name '{' '}'                      { at $1 $3 (Struct $1 Nothing []) }
  | name '{' SepEndBy1(';',field) '}' { at $1 $4 (Struct $1 Nothing $3) }
  | name '{' name 'with' SepEndBy1(';',field) '}'
                                      { at $1 $6 (Struct $1 (Just $3) $5) }

  | '(' ')'                           { at $1 $2 (Tuple []) }
  | '(' expression ')'                { at $1 $3 $2 }
  | '(' expression ',' exprList ')'   { at $1 $3 (Tuple ($2 : $4)) }


mergeCase :: { (SourceRange, MergeCase) }
  : '(' mergePat '->' expression ')'  { ($1 <-> $5, MergeCase $2 $4) }

mergePat :: { Expression }
  : name                              { Var $1 }
  | BOOL                              { toLit $1 }

simpExpr :: { Expression }
  : INT                                       { toLit $1 }
  | REAL                                      { toLit $1 }
  | BOOL                                      { toLit $1 }
  | name                                      { Var $1   }
  | 'not'     simpExpr                        { toE1 Not      $1 $2 }
  | '-'       simpExpr %prec UMINUS           { toE1 Neg      $1 $2 }

  | simpExpr 'and' simpExpr                   { toE2 $1 $2 And      $3 }
  | simpExpr 'or' simpExpr                    { toE2 $1 $2 Or       $3 }
  | simpExpr 'xor' simpExpr                   { toE2 $1 $2 Xor      $3 }
  | simpExpr '=>' simpExpr                    { toE2 $1 $2 Implies  $3 }
  | simpExpr '=' simpExpr                     { toE2 $1 $2 Eq       $3 }
  | simpExpr '<>' simpExpr                    { toE2 $1 $2 Neq      $3 }
  | simpExpr '<' simpExpr                     { toE2 $1 $2 Lt       $3 }
  | simpExpr '<=' simpExpr                    { toE2 $1 $2 Leq      $3 }
  | simpExpr '>' simpExpr                     { toE2 $1 $2 Gt       $3 }
  | simpExpr '>=' simpExpr                    { toE2 $1 $2 Geq      $3 }
  | simpExpr 'div' simpExpr                   { toE2 $1 $2 Div      $3 }
  | simpExpr 'mod' simpExpr                   { toE2 $1 $2 Mod      $3 }
  | simpExpr '-' simpExpr                     { toE2 $1 $2 Sub      $3 }
  | simpExpr '+' simpExpr                     { toE2 $1 $2 Add      $3 }
  | simpExpr '/' simpExpr                     { toE2 $1 $2 Div      $3 }
  | simpExpr '*' simpExpr                     { toE2 $1 $2 Mul      $3 }
  | simpExpr '**' simpExpr                    { toE2 $1 $2 Power    $3 }

  | 'if' simpExpr
      'then' simpExpr
      'else' simpExpr                         { toITE $1 $2 $4 $6 }

  | '(' ')'                                   { at $1 $2 (Tuple []) }
  | '(' simpExpr ')'                          { at $1 $3 $2 }
  | '(' simpExpr ',' SepBy1(',',simpExpr) ')' { at $1 $3 (Tuple ($2 : $4)) }


field :: { Field }
  : ident '=' expression              { Field $1 $3 }

clockExpr :: { ClockExpr }
  : name '(' ident ')'    { WhenClock ($1 <-> $4) (Var $1) $3 }
  | ident                 { WhenClock (range $1)  (Lit (Bool True)) $1  }
  | 'not' ident           { WhenClock ($1 <-> $2) (Lit (Bool False)) $2 }
  | 'not' '(' ident ')'   { WhenClock ($1 <-> $4) (Lit (Bool False)) $3 }

arraySel :: { Selector Expression }
  : expression                        { SelectElement $1 }
  | arraySlice                        { SelectSlice $1 }

arraySlice :: { ArraySlice Expression }
  : expression '..' expression Opt(step) { ArraySlice $1 $3 $4 }

step :: { Expression }
  : 'step' expression                 { $2 }

exprList :: { [Expression] }
  : SepBy1(',',expression)            { $1 }
  | {- empty -}                       { [] }

effNode :: { NodeInst }
  : name                                          { toNodeInst $1 [] }
  | name '<<' SepBy1(staticArgSep,staticArg) '>>' { toNodeInst $1 $3 }


-- Static Arguments ------------------------------------------------------------
-- The specific value for a static parameter.

staticArgSep :: { () }
  : ';' { () }
  | ',' { () }

staticArg :: { StaticArg }
  : staticArgGen(noName) { snd $1 }

noName :: { () }
  : {- empty -}                       { () }


staticNamedArg :: { (Ident, StaticArg) }
  : staticArgGen(withName)            { $1 }

withName :: { Ident }
  : ident '='                         { $1 }

staticArgGen(nm) :: { (nm,StaticArg) }
  : 'type' nm type                       { ($2, TypeArg $3)     }
  | 'const' nm expression                { ($2, ExprArg $3)     }
  | nodeType nm effNode                  { ($2, NodeArg $1 $3)  }
  | nm 'not'                             { ($1, op1Arg $2 Not)     }
  | nm 'fby'                             { ($1, op2Arg $2 Fby)     }
  | nm 'pre'                             { ($1, op1Arg $2 Pre)     }
  | nm 'current'                         { ($1, op1Arg $2 Current) }
  | nm '->'                              { ($1, op2Arg $2 FbyArr)  }
  | nm 'and'                             { ($1, op2Arg $2 And)     }
  | nm 'or'                              { ($1, op2Arg $2 Or)      }
  | nm 'xor'                             { ($1, op2Arg $2 Xor)     }
  | nm '=>'                              { ($1, op2Arg $2 Implies) }
  | nm '='                               { ($1, op2Arg $2 Eq)      }
  | nm '<>'                              { ($1, op2Arg $2 Neq)     }
  | nm '<'                               { ($1, op2Arg $2 Lt)      }
  | nm '<='                              { ($1, op2Arg $2 Leq)     }
  | nm '>'                               { ($1, op2Arg $2 Gt)      }
  | nm '>='                              { ($1, op2Arg $2 Geq)     }
  | nm 'div'                             { ($1, op2Arg $2 Div)     }
  | nm 'mod'                             { ($1, op2Arg $2 Mod)     }
  | nm '-'                               { ($1, op2Arg $2 Sub)     }
  | nm '+'                               { ($1, op2Arg $2 Add)     }
  | nm '/'                               { ($1, op2Arg $2 Div)     }
  | nm '*'                               { ($1, op2Arg $2 Mul)     }
  | nm 'if'                              { ($1, opIf $2)           }
  | nm name '<<' SepBy1(staticArgSep,staticArg) '>>'
                                    { ($1, NodeArg Node (toNodeInst $2 $4) )}
  | nm simpleType                        { ($1, TypeArg $2) }
  | nm simpExpr                          { ($1, ExprArg $2) }


-- Names and Identifiers -------------------------------------------------------

name :: { Name }
  : ident                 { Unqual $1 }
  | QIDENT                { toQIdent $1 }

ident :: { Ident }
  : IDENT                 { toIdent $1 [] }
  | IDENT ListOf1(pragma) { toIdent $1 $2 }

pragma :: { Pragma }
  : '%' IDENT ':' IDENT '%' { Pragma { pragmaTextA = lexemeText $2
                                     , pragmaTextB = lexemeText $4
                                     , pragmaRange = $1 <-> $5 } }

-- Combinators -----------------------------------------------------------------


Perhaps(x) :: { Bool }
  : {- nothing -}       { False }
  | x                   { True  }

Opt(x) :: { Maybe x }
  : {- nothing -}       { Nothing }
  | x                   { Just $1 }


ListOf1(thing) :: { [thing] }
  : ListOf1_rev(thing) { reverse $1 }

ListOf1_rev(thing) :: { [thing] }
  : thing                           { [$1] }
  | ListOf1_rev(thing) thing        { $2 : $1 }

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


SepEndBy1(sep,thing) :: { [thing] }
  : thing                           { [$1] }
  | thing ';'                       { [$1] }
  | thing ';' SepEndBy1(sep,thing)  { $1 : $3 }




{

class At t where
  at :: (HasRange a, HasRange b) => a -> b -> t -> t

instance At Expression where
  at x y = ERange (x <-> y)

instance At Type where
  at x y = TypeRange (x <-> y)

instance At StaticArg where
  at x y  = ArgRange (x <-> y)

--------------------------------------------------------------------------------

toE1 :: Op1 -> SourceRange -> Expression -> Expression
toE1 op rng expr = ERange (rng <-> expr) (callPrim rng (Op1 op) [expr])

toE2 :: Expression -> SourceRange -> Op2 -> Expression -> Expression
toE2 e1 rng op e2 = ERange (e1 <-> e2) (callPrim rng (Op2 op) [e1,e2])

toEN :: OpN -> SourceRange -> SourceRange -> [Expression] -> Expression
toEN op r1 r2 es = ERange (r1 <-> r2) (callPrim r1 (OpN op) es)

toITE :: SourceRange -> Expression -> Expression -> Expression -> Expression
toITE r e1 e2 e3 = ERange (r <-> e3) (callPrim r ITE [e1,e2,e3])

--------------------------------------------------------------------------------

toIdent :: Lexeme Token -> [Pragma] -> Ident
toIdent l ps = Ident { identText    = lexemeText l
                     , identRange   = lexemeRange l
                     , identPragmas = ps
                     }

toQIdent :: Lexeme Token -> Name
toQIdent l =
  case lexemeToken l of
    TokQualIdent p n -> Qual (lexemeRange l) p n
    _ -> panic "toQIdent" [ "Not a qualified identifier", show l ]

toLit :: Lexeme Token -> Expression
toLit l =
  ERange (lexemeRange l) $
  Lit $
  case lexemeToken l of
    TokInt n    -> Int n
    TokReal n   -> Real n
    TokBool n   -> Bool n
    _           -> panic "toLit" [ "Unexcpected literal", show l ]

toMerge :: SourceRange -> Ident -> [(SourceRange,MergeCase)] -> Expression
toMerge r1 x opts = at r1 (last rs) (Merge x cs)
  where
  (rs,cs) = unzip opts

--------------------------------------------------------------------------------

toTypeDecl :: Ident -> Maybe TypeDef -> TypeDecl
toTypeDecl i d = TypeDecl { typeName = i, typeDef = d }

class ToFieldType t where
  toFieldType :: t -> [FieldType]

instance ToFieldType (Ident, Type, Expression) where
  toFieldType (x,t,e) = [ FieldType { fieldName = x, fieldType = t
                                    , fieldDefault = Just e } ]

instance ToFieldType (Ident, Type) where
  toFieldType (x,t) = [ FieldType { fieldName = x, fieldType = t
                                  , fieldDefault = Nothing } ]

instance ToFieldType (Ident, [Ident], Type) where
  toFieldType (i,is,t) = [ d | x <- i : is, d <- toFieldType (x,t) ]

--------------------------------------------------------------------------------

class ToConstDef t where
  toConstDef :: t -> [ ConstDef ]

instance ToConstDef (Ident, Type) where
  toConstDef (i,t) = [ ConstDef { constName = i
                                , constType = Just t
                                , constDef = Nothing
                                } ]

instance ToConstDef (Ident, [Ident], Type) where
  toConstDef (i, is, t) = [ d | x <- i:is, d <- toConstDef (i,t) ]

instance ToConstDef (Ident,Expression) where
  toConstDef (i,e) = [ ConstDef { constName = i
                                , constType = Nothing
                                , constDef  = Just e
                                } ]

instance ToConstDef (Ident,Type,Expression) where
  toConstDef (i,t,e) = [ ConstDef { constName = i
                                  , constType = Just t
                                  , constDef  = Just e
                                  } ]

--------------------------------------------------------------------------------

toVarDeclBase :: ([Ident], Type) -> [ Binder ]
toVarDeclBase (xs,t) = [ Binder { binderDefines = x
                                , binderType    = t
                                , binderClock   = Nothing
                                } | x <- xs ]

toVarDecl :: ([Ident], Type) -> ClockExpr -> [ Binder ]
toVarDecl (xs,t) c = [ Binder { binderDefines = x
                              , binderType    = t
                              , binderClock   = Just c
                              } | x <- xs ]

isUnsafe :: Bool -> Safety
isUnsafe unsafe = if unsafe then Unsafe else Safe

--------------------------------------------------------------------------------

toNodeInst :: Name -> [ StaticArg ] -> NodeInst
toNodeInst nm xs = NodeInst c xs
  where
  c = case nm of
        Unqual i
          -- XXX: Use KW? Or maybe just use names everywhere and
          -- identify built-ins in some name resultion pass...
          | txt == "fill"     -> iter IterFill
          | txt == "red"      -> iter IterRed
          | txt == "fillred"  -> iter IterFillRed
          | txt == "map"      -> iter IterMap
          | txt == "boolred"  -> iter IterBoolRed
          where
          txt  = identText i
          iter x = CallPrim (identRange i) (Iter x)
        _ -> CallUser nm

primArg :: SourceRange -> PrimNode -> StaticArg
primArg r p = NodeArg Function (NodeInst (CallPrim r p) [])

op1Arg :: SourceRange -> Op1 -> StaticArg
op1Arg r p = primArg r (Op1 p)
op2Arg r p = primArg r (Op2 p)
opIf r     = primArg r ITE

-- | Call a primitive with no static parameters
callPrim :: SourceRange -> PrimNode -> [Expression] -> Expression
callPrim r p es = CallPos (NodeInst (CallPrim r p) []) es




--------------------------------------------------------------------------------

-- | Parse a program from the given source.
-- We throw a 'ParseError' exception if we fail to parse a program.
parseProgramFrom :: Text    {- ^ Label for parse errors -} ->
                    IO Text {- ^ The text to parse -} ->
                    IO Program {- ^ The parsed program, or exception -}
parseProgramFrom lab io =
  do txt <- io
     case parse program lab txt of
       Left err -> throwIO err
       Right a  -> pure a

-- | Parse a program from a UTF-8 encoded file.
-- May throw 'ParseEror' or exceptions related to reading and decoding the file.
parseProgramFromFileUTF8 :: FilePath -> IO Program
parseProgramFromFileUTF8 file =
  parseProgramFrom (Text.pack file) (Text.readFile file)

-- | Parse a program from a Latin-1 encoded file.
-- May throw 'ParseEror' or exceptions related to reading and decoding the file.
parseProgramFromFileLatin1 :: FilePath -> IO Program
parseProgramFromFileLatin1 file =
  parseProgramFrom (Text.pack file) (Text.decodeLatin1 <$> BS.readFile file)

}
