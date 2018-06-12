{
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Lustre.Lexer
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
import Data.Char(isAscii,toLower)
import Data.Ratio((%))

import AlexTools
}


$letter         = [a-zA-Z_]
$octdigit       = 0-7
$digit          = 0-9
$digitNZ        = 1-9
$hexdigit       = [0-9a-fA-F]

@ident          = $letter ($letter | $digit)*
@qident         = @ident "::" @ident

@digs8          = [0-7]+
@digs10         = [0-9]+
@digs16         = [0-9A-Fa-f]+

@sign           = [\+\-]
@num8           = @sign? "0o" @digs8
@num10          = @sign? @digs10
@num16          = @sign? "0x" @digs16


@exp10          = [Ee] @num10
@exp16          = [Pp] @num10
@float10        = @num10 @exp10
                | (@num10 "." @digs10?) @exp10?
                | (@sign? @digs10? "." @digs10) @exp10?
@float16        = @num16 @exp16
                | (@num16 "." @digs16?) @exp16?
                | (@sign? "0x" @digs16? "." @digs16) @exp16?

@line_comment   = "--".*
@block_comment  = "/*" (. | \n)* "*/"
:-

$white+         { return [] }
@line_comment   { return [] }
@block_comment  { return [] }

"::"            { lexeme TokColon }

@ident          { lexeme TokIdent }
@num8           { lexeme' . TokInt  . integerAtBase 8  =<< matchText }
@num10          { lexeme' . TokInt  . integerAtBase 10 =<< matchText }
@num16          { lexeme' . TokInt  . integerAtBase 16 =<< matchText }
@float10        { lexeme' . TokReal . floating 10 =<< matchText }
@float16        { lexeme' . TokReal . floating 16 =<< matchText }
.               { lexeme TokError }

{

data Token =
    TokIdent

  | TokInt !Integer
  | TokReal !Rational

  | TokColon

  | TokEOF
  | TokError
    deriving Show

lexeme' :: Token -> Action () [Lexeme Token]
lexeme' t = lexeme $! t

integerAtBase :: Integer -> Text -> Integer
integerAtBase base txt = if sgn == "-" then negate aval else aval
  where
  aval = Text.foldl' addDig 0 digs
  (sgn,txt0) = Text.span (\x -> x == '+' || x == '-') (Text.map toLower txt)
  digs = Text.dropWhile (\x -> x == '0' || x == 'x' || x == 'o') txt0

  addDig s x = s * base + (if y < a then y - z else 10 + (y - a))
    where
    y = val x
    a = val 'a'
    z = val '0'
    val = fromIntegral . fromEnum

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
    case Text.splitOn "." base of
      [x]    -> fromInteger (integerAtBase dbase x)
      [x,y]  -> fromInteger (integerAtBase dbase x) +
               (integerAtBase dbase y) % (fromInteger dbase ^ Text.length y)
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


