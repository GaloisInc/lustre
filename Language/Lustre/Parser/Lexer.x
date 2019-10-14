{
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Lustre.Parser.Lexer
  ( lexer
  , Lexeme(..)
  , Token(..)
  , Input(..), initialInput
  , SourceRange(..)
  , SourcePos(..)
  , prettySourceRange
  ) where
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Map as Map
import Data.Char(isAscii,toLower)
import Data.Ratio((%))

import AlexTools
}


$letter         = [a-zA-Z_]
$octdigit       = 0-7
$digit          = 0-9
$hexdigit       = [0-9a-fA-F]

@ident          = $letter ($letter | $digit)*
@qident         = @ident "::" @ident

@digs8          = [0-7]+
@digs16         = [0-9A-Fa-f]+

@sign           = [\+\-]
@num8           = "0o" @digs8
@num10          = [0-9]+
@num16          = "0x" @digs16


@exp10          = [Ee] @sign? @num10
@exp16          = [Pp] @sign? @num10
@float10        = @num10 @exp10
                | (@num10  "." @num10?) @exp10?
                | (@num10? "." @num10)  @exp10?
@float16        = @num16 @exp16
                | (@num16        "." @digs16?) @exp16?
                | ("0x" @digs16? "." @digs16) @exp16?

@line_comment    = "--"[^\%].* | "--"
@special_comment = "--%"($letter|$digit)*
@not_star        = \n | ~\*


@not_cparen     = [^\*\)] | \n
@block1_cont    = @not_star | ("*"+ @not_cparen)
@block_comment1 = "(*" [^@] @block1_cont* "*"+ ")"

@not_fslash     = [^\*\/] | \n
@block2_cont    = @not_star | "*"+ @not_fslash
@block_comment2 = "/*" [^@] @block2_cont* "*"+ "/"
:-

$white+         { return [] }
@line_comment   { return [] }
@block_comment1 { return [] }
@block_comment2 { return [] }

@special_comment    { specialComment }

"/*@contract"       { lexeme TokStartSlashCommentContract }
"*/"                { lexeme TokEndSlashComment }
"(*@contract"       { lexeme TokStartParenCommentContract }
"*)"                { lexeme TokEndParenComment }

"package"           { lexeme TokKwPackage }
"model"             { lexeme TokKwModel }
"uses"              { lexeme TokKwUses }
"needs"             { lexeme TokKwNeeds }
"provides"          { lexeme TokKwProvides }
"is"                { lexeme TokKwIs }
"body"              { lexeme TokKwBody }
"end"               { lexeme TokKwEnd }

"when"              { lexeme TokKwWhen }
"current"           { lexeme TokKwCurrent }
"currentWith"       { lexeme TokKwCurrentWith }
"condact"           { lexeme TokKwCondact }
"callWhen"          { lexeme TokKwCallWhen }
"pre"               { lexeme TokKwPre }
"fby"               { lexeme TokKwFby }
"->"                { lexeme TokRightArrow }

"div"               { lexeme TokKwDiv }
"mod"               { lexeme TokKwMod }
"+"                 { lexeme TokPlus }
"-"                 { lexeme TokMinus }
"*"                 { lexeme TokStar }
"**"                { lexeme TokStarStar }
"/"                 { lexeme TokDiv }


"with"              { lexeme TokKwWith }
"if"                { lexeme TokKwIf }
"else"              { lexeme TokKwElse }
"then"              { lexeme TokKwThen }
"merge"             { lexeme TokKwMerge }

"step"              { lexeme TokKwStep }
".."                { lexeme TokDotDot }
"|"                 { lexeme TokBar }
"^"                 { lexeme TokHat }

"#"                 { lexeme TokHash }
"not"               { lexeme TokKwNot }
"xor"               { lexeme TokKwXor }
"or"                { lexeme TokKwOr }
"and"               { lexeme TokKwAnd }
"nor"               { lexeme TokKwNor }
"true"              { lexeme (TokBool True) }
"false"             { lexeme (TokBool False) }

"=>"                { lexeme TokImplies }
"<"                 { lexeme TokLt }
"<="                { lexeme TokLeq }
"="                 { lexeme TokEq }
">="                { lexeme TokGeq }
">"                 { lexeme TokGt }
"<>"                { lexeme TokNotEq }
":="                { lexeme TokColonEq }


"int"               { lexeme TokKwInt }
"real"              { lexeme TokKwReal }
"bool"              { lexeme TokKwBool }
"floor"             { lexeme TokKwFloor }         -- jkind
"subrange"          { lexeme TokKwSubrange }    -- jkind
"of"                { lexeme TokKwOf }          -- jkind

"unsafe"            { lexeme TokKwUnsafe }
"extern"            { lexeme TokKwExtern }
"imported"          { lexeme TokKwImported }
"node"              { lexeme TokKwNode }
"function"          { lexeme TokKwFunction }
"returns"           { lexeme TokKwReturns }

"type"              { lexeme TokKwType }
"const"             { lexeme TokKwConst }
"var"               { lexeme TokKwVar }
"struct"            { lexeme TokKwStruct }
"enum"              { lexeme TokKwEnum }
"contract"          { lexeme TokKwContract }
"import"            { lexeme TokKwImport }
"assert"            { lexeme TokKwAssert }
"assume"            { lexeme TokKwAssume }
"guarantee"         { lexeme TokKwGuarantee }
"mode"              { lexeme TokKwEnsure }
"require"           { lexeme TokKwRequire }
"ensure"            { lexeme TokKwEnsure }

"%"                 { lexeme TokMod }
":"                 { lexeme TokColon }
","                 { lexeme TokComma }
";"                 { lexeme TokSemi }
"."                 { lexeme TokDot }
"("                 { lexeme TokOpenParen }
")"                 { lexeme TokCloseParen }
"<<"                { lexeme TokOpenTT }
">>"                { lexeme TokCloseTT }
"["                 { lexeme TokOpenBracket }
"]"                 { lexeme TokCloseBracket }
"{"                 { lexeme TokOpenBrace }
"}"                 { lexeme TokCloseBrace }
"let"               { lexeme TokKwLet }
"tel"               { lexeme TokKwTel }

@ident              { lexeme TokIdent }
@ident "::" @ident  { qualIdent }
@num8               { lexeme' . TokInt  . integerAtBase 8  =<< matchText }
@num10              { lexeme' . TokInt  . integerAtBase 10 =<< matchText }
@num10 ".."         { numDotDot } -- to avoid conflict with slices
@num16              { lexeme' . TokInt  . integerAtBase 16 =<< matchText }
@float10            { lexeme' . TokReal . floating 10 =<< matchText }
@float16            { lexeme' . TokReal . floating 16 =<< matchText }

.                   { lexeme TokError }


{

data Token =
    TokIdent
  | TokQualIdent Text Text
  | TokInt !Integer
  | TokReal !Rational

  | TokKwPackage | TokKwModel
  | TokKwIs
  | TokKwUses | TokKwNeeds | TokKwProvides
  | TokKwBody | TokKwEnd

  | TokKwIf | TokKwThen | TokKwElse
  | TokKwWith | TokKwMerge


  | TokKwExtern
  | TokKwUnsafe
  | TokKwImported
  | TokKwNode
  | TokKwFunction
  | TokKwReturns

  | TokKwType
  | TokKwConst
  | TokKwVar
  | TokKwLet
  | TokKwTel
  | TokKwStruct
  | TokKwEnum

  | TokKwContract
  | TokKwAssert
  | TokKwAssume
  | TokKwGuarantee
  | TokKwMode
  | TokKwRequire
  | TokKwEnsure
  | TokKwImport
  | TokStartSlashCommentContract
  | TokEndSlashComment
  | TokStartParenCommentContract
  | TokEndParenComment



  | TokKwCurrent
  | TokKwCurrentWith
  | TokKwCondact
  | TokKwCallWhen
  | TokKwPre
  | TokKwWhen

  | TokKwAnd
  | TokKwNot
  | TokKwOr
  | TokKwXor
  | TokKwNor
  | TokBool Bool

  | TokKwDiv
  | TokKwMod

  | TokKwInt
  | TokKwReal
  | TokKwBool
  | TokKwFloor

  | TokKwStep
  | TokKwFby

  | TokPragmaProperty
  | TokPragmaMain
  | TokPragmaIVC
  | TokPragmaRealizable

  | TokColon
  | TokComma
  | TokSemi
  | TokDot
  | TokDotDot
  | TokColonEq

  | TokOpenParen
  | TokCloseParen
  | TokOpenTT
  | TokCloseTT
  | TokOpenBracket
  | TokCloseBracket
  | TokOpenBrace
  | TokCloseBrace

  | TokRightArrow
  | TokImplies
  | TokLt | TokLeq | TokEq | TokGeq | TokGt | TokNotEq
  | TokPlus | TokMinus | TokStar | TokStarStar | TokDiv | TokMod
  | TokHash
  | TokHat
  | TokBar

  | TokKwSubrange
  | TokKwOf

  | TokEOF
  | TokError
    deriving (Eq,Show)


lexeme' :: Token -> Action () [Lexeme Token]
lexeme' t = lexeme $! t

numDotDot :: Action s [ Lexeme Token ]
numDotDot =
  do (num,dots) <- Text.break (== '.') <$> matchText
     SourceRange { sourceFrom = from, sourceTo = to } <- matchRange
     let mid = prevPos to
     return [ Lexeme { lexemeText  = num
                     , lexemeToken = TokInt (integerAtBase 10 num)
                     , lexemeRange = SourceRange { sourceFrom = from
                                                 , sourceTo = prevPos mid } }
            , Lexeme { lexemeText  = dots
                     , lexemeToken = TokDotDot
                     , lexemeRange = SourceRange { sourceFrom = mid
                                                 , sourceTo = to } }
            ]

specialComment :: Action s [ Lexeme Token ]
specialComment =
  do txt <- matchText
     rng <- matchRange
     pure [ Lexeme { lexemeText = txt
                   , lexemeToken = Map.findWithDefault TokError txt known
                   , lexemeRange = rng } ]
  where
  known = Map.fromList [ ("--%PROPERTY", TokPragmaProperty)
                       , ("--%MAIN", TokPragmaMain)
                       , ("--%IVC", TokPragmaIVC)
                       , ("--%REALIZABLE", TokPragmaRealizable)
                       ]

qualIdent :: Action s [ Lexeme Token ]
qualIdent =
  do ~[a,b] <- Text.splitOn "::" <$> matchText
     lexeme (TokQualIdent a b)

integerAtBase :: Integer -> Text -> Integer
integerAtBase base txt = if sgn == "-" then negate aval else aval
  where
  aval = Text.foldl' addDig 0 digs
  (sgn,txt0) = splitSign (Text.map toLower txt)
  digs = Text.dropWhile (\x -> x == '0' || x == 'x' || x == 'o') txt0

  addDig s x = s * base + (if y < a then y - z else 10 + (y - a))
    where
    y = val x
    a = val 'a'
    z = val '0'
    val = fromIntegral . fromEnum

splitSign :: Text -> (Text,Text)
splitSign = Text.span (\x -> x == '+' || x == '-')

floating :: Integer -> Text -> Rational
floating fb txt =
  case Text.splitOn exSym (Text.map toLower txt) of
    [base] -> parseBase base
    [base,ex]
      | e >= 0    -> b * fromInteger exVal ^ e
      | otherwise -> b / fromInteger exVal ^ abs e
        where
        e = integerAtBase 10 ex
        b = parseBase base

    _ -> error "[bug] unexpected floating number"
  where
  (exSym,exVal,dbase) = if fb == 10 then ("e",10,10) else ("p",2,16)

  parseBase base =
    let (sign,rest) = splitSign base
        addSign = if sign == "-" then negate else id
    in addSign
     $ case Text.splitOn "." rest of
         [x]    -> fromInteger (integerAtBase dbase x)
         [x,y]  -> fromInteger (integerAtBase dbase x) + 
                   integerAtBase dbase y % dbase ^ Text.length y
         _ -> error "[bug] unexpected floating number base"


alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte = makeAlexGetByte toByte
  where
  toByte ch | isAscii ch = fromIntegral (fromEnum ch)
            | otherwise  = 0   -- Should cause an error token to be emitted

lexer :: Input -> [Lexeme Token]
lexer = $makeLexer simpleLexer { lexerEOF = \_ p -> [eof p] }
  where eof p = Lexeme { lexemeToken = TokEOF
                       , lexemeText  = ""
                       , lexemeRange = AlexTools.range p
                       }
}


