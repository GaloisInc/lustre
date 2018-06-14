{
module Language.Lustre.Parser
  ( parse, parseStartingAt
  , program, expression
  ) where

import AlexTools(HasRange(range), (<->))

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

  'when'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwWhen } }
  'current'   { Lexeme { lexemeRange = $$, lexemeToken = TokKwCurrent } }
  'pre'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwPre } }
  'fby'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwFby } }
  '->'        { Lexeme { lexemeRange = $$, lexemeToken = TokRightArrow } }

  'div'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwDiv } }
  'mod'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwMod } }
  '+'         { Lexeme { lexemeRange = $$, lexemeToken = TokPlus } }
  '-'         { Lexeme { lexemeRange = $$, lexemeToken = TokMinus } }
  '*'         { Lexeme { lexemeRange = $$, lexemeToken = TokTimes } }
  '/'         { Lexeme { lexemeRange = $$, lexemeToken = TokDiv } }


  'step'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwStep } }
  '|'         { Lexeme { lexemeRange = $$, lexemeToken = TokBar } }
  '^'         { Lexeme { lexemeRange = $$, lexemeToken = TokHat } }
  '..'        { Lexeme { lexemeRange = $$, lexemeToken = TokDotDot } }

  'int'       { Lexeme { lexemeRange = $$, lexemeToken = TokKwInt } }
  'real'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwReal } }
  'bool'      { Lexeme { lexemeRange = $$, lexemeToken = TokKwBool } }


  ':'         { Lexeme { lexemeRange = $$, lexemeToken = TokColon } }
  '::'        { Lexeme { lexemeRange = $$, lexemeToken = TokColonColon } }
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
  : topDecl { undefined}

topDecl :: { [TopDecl] }
  : 'const' EndBy1(';',constDef)     { map DeclareConst (concat $2) }
  | 'type' EndBy1(';',typeDecl)      { $2 }
  | extDecl                          { [ DeclareNode $1 ] }
  | nodeDecl                         { [ DeclareNode $1 ] }


-- Constant Declarations -------------------------------------------------------

constDef :: { [ConstDef] }
  : ident ':' type                        { toConstDef ($1,$3) }
  | ident ',' SepBy1(',',ident) ':' type  { toConstDef ($1,$3,$5) }
  | ident '=' expression                  { toConstDef ($1,$3) }
  | ident ':' type '=' expression         { toConstDef ($1,$3,$5) }


-- Type Declarations -----------------------------------------------------------

typeDecl :: { TopDecl }
  : ident                                     { toTypeDecl $1 IsAbstract }
  | ident '=' typeDef                         { toTypeDecl $1 $3 }

typeDef :: { TypeDef }
  : type                                      { IsType $1 }
  | 'enum' '{' SepBy1(',',ident) '}'          { IsEnum $3 }
  | Perhaps('struct') '{' SepBy1(';',fieldType) '}'   { IsStruct (concat $3) }


fieldType :: { [FieldType] }
  : ident ':' type '=' expression             { toFieldType ($1,$3,$5) }
  | ident ':' type                            { toFieldType ($1,$3) }
  | ident ',' SepBy1(',',ident) ':' type      { toFieldType ($1, $3, $5) }


-- Types -----------------------------------------------------------------------

type :: { Type }
  : baseType                                  { $1 }
  | type '^' expression                       { at $1 $3 (ArrayType $1 $3) }

baseType :: { Type }
  : 'int'                                     { at $1 $1 IntType       }
  | 'real'                                    { at $1 $1 RealType      }
  | 'bool'                                    { at $1 $1 BoolType      }
  | name                                      { NamedType $1           }


-- Node Declarations -----------------------------------------------------------

extDecl :: { NodeDecl }
  : Perhaps('unsafe') 'extern' nodeType
    ident params 'returns' params
      { NodeDecl
          { nodeUnsafe  = $1
          , nodeExtern  = True
          , nodeType    = $3
          , nodeName    = $4
          , nodeInputs  = $5
          , nodeOutputs = $7
          , nodePragmas = []
          , nodeDef     = Nothing
          }
      }



nodeDecl :: { NodeDecl }
  : Perhaps('unsafe') nodeType
    ident params 'returns' params Perhaps(';')
    localDecls body
      { NodeDecl
          { nodeUnsafe  = $1
          , nodeExtern  = False
          , nodeType    = $2
          , nodeName    = $3
          , nodeInputs  = $4
          , nodeOutputs = $6
          , nodePragmas = []
          , nodeDef     = Just NodeBody { nodeLocals = $8
                                        , nodeEqns   = $9
                                        }
          }
      }

nodeType :: { NodeType }
  : 'node'      { Node }
  | 'function'  { Function }

localDecls :: { [LocalDecl] }
  : {- empty -}                            { [] }
  | ListOf1(localDecl)                     { concat $1 }

localDecl :: { [LocalDecl] }
  : 'var' EndBy1(';',varDecl)              { map LocalVar (concat $2) }
  | 'const' EndBy1(';',constDef)           { map LocalConst (concat $2) }

body :: { [Equation] }
  : 'let' {-XXX-} 'tel'                    { [] }

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

  | '#' '(' exprList ')'             { at $1 $4 (EOpN AtMostOne $3) }
  | 'nor' '(' exprList ')'           { at $1 $4 (EOpN Nor $3) }

  | '[' exprList ']'                 { at $1 $3 (Array $2) }

  | expression '[' arraySel ']'       { at $1 $4 (Select $1 $3) }
  | expression '.' ident              { at $1 $3 (Select $1 (SelectField $3))}

  | name '(' exprList ')'            { at $1 $4 (CallPos (NodeName $1 []) $3) }

clockExpr :: { ClockExpr }
  : name '(' ident ')'                { WhenClock ($1 <-> $4) (ClockIs $1) $3 }
  | ident                             { WhenClock (range $1)  ClockIsTrue $1  }
  | 'not' ident                       { WhenClock ($1 <-> $2) ClockIsFalse $2 }
  | 'not' '(' ident ')'               { WhenClock ($1 <-> $4) ClockIsFalse $3 }

arraySel :: { Selector }
  : expression                        { SelectElement $1 }
  | arraySlice                        { SelectSlice $1 }

arraySlice :: { ArraySlice }
  : expression '..' expression Opt(step) { ArraySlice $1 $3 $4 }

step :: { Expression }
  : 'step' expression                 { $2 }

exprList :: { [Expression] }
  : SepBy1(',',expression)          { $1 }


-- Names and Identifiers -------------------------------------------------------

name :: { Name }
  : ident                 { Unqual $1 }
  | ident '::' ident      { Qual $1 $3 }

ident :: { Ident }
  : IDENT                 { toIdent $1 }


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

--------------------------------------------------------------------------------

toE1 :: Op1 -> SourceRange -> Expression -> Expression
toE1 op rng expr = at rng expr (EOp1 op expr)

toE2 :: Op2 -> Expression -> Expression -> Expression
toE2 op e1 e2 = EOp2 e1 op e2

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

toTypeDecl :: Ident -> TypeDef -> TopDecl
toTypeDecl i d = DeclareType TypeDecl { typeName = i, typeDef = d }

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
                                , constPragmas = []
                                } ]

instance ToConstDef (Ident, [Ident], Type) where
  toConstDef (i, is, t) = [ d | x <- i:is, d <- toConstDef (i,t) ]

instance ToConstDef (Ident,Expression) where
  toConstDef (i,e) = [ ConstDef { constName = i
                                , constType = Nothing
                                , constDef  = Just e
                                , constPragmas = []
                                } ]

instance ToConstDef (Ident,Type,Expression) where
  toConstDef (i,t,e) = [ ConstDef { constName = i
                                  , constType = Just t
                                  , constDef  = Just e
                                  , constPragmas = []
                                  } ]

--------------------------------------------------------------------------------

toVarDeclBase :: ([Ident], Type) -> [ Binder ]
toVarDeclBase (xs,t) = [ Binder { binderDefines = x
                                , binderType    = t
                                , binderClock   = BaseClock (range x)
                                , binderPragmas = []
                                } | x <- xs ]

toVarDecl :: ([Ident], Type) -> ClockExpr -> [ Binder ]
toVarDecl (xs,t) c = [ Binder { binderDefines = x
                              , binderType    = t
                              , binderClock   = c
                              , binderPragmas = []
                              } | x <- xs ]


}
