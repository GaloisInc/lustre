{-# Language OverloadedStrings #-}
module Language.Lustre.Parser.Monad
  ( Parser
  , parseStartingAt
  , parse
  , happyGetToken
  , happyError
  , happyErrorAt
  , ParseError(..)
  ) where

import Control.Monad(liftM,ap)
import Control.Exception (Exception)
import Data.Text(Text)
import AlexTools(prevPos, startPos, range)
import Text.PrettyPrint

import Language.Lustre.Parser.Lexer
import Language.Lustre.Pretty
import Language.Lustre.Panic

newtype Parser a = Parser (PState -> Either ParseError (a, PState))

data PState = PState
  { curToken   :: Maybe (Lexeme Token)
  , nextToknes :: [Lexeme Token]
  }

{-| Run the given parser on the input text. We always try to parse the
whole text, starting at the input, and report an error if there was
left-overs at the end.

The given source position should correspond to the first character in
the text. -}
parseStartingAt ::
  Parser a  {- ^ Describes how to parse the input -} ->
  SourcePos {- ^ Location for the first character in the text -} ->
  Text      {- ^ Parse this text -} ->
  Either ParseError a
parseStartingAt (Parser m) p txt =
  case m s0 of
    Left err -> Left err
    Right (a,sFin) ->
      case nextToknes sFin of
        []    -> Right a
        l : _ -> Left $ ParseError $ lexemeRange l
  where
  s0 = PState { curToken = Nothing, nextToknes = lexer input }

  input = Input { inputPos       = p
                , inputText      = txt
                , inputPrev      = pPos
                , inputPrevChar  =
                    if sourceLine pPos == sourceLine p then ' ' else '\n'
                }
  pPos  = prevPos p

parse :: Parser a {- ^ Describes how to parse -} ->
         Text     {- ^ Name for the input text (e.g., file name) -} ->
         Text     {- ^ The text to parse -} ->
         Either ParseError a
parse p inp = p `parseStartingAt` startPos inp




instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure a = Parser (\ls -> Right (a,ls))
  (<*>)  = ap

instance Monad Parser where
  Parser m >>= k = Parser (\ls -> case m ls of
                                    Left err -> Left err
                                    Right (a,ls1) ->
                                      let Parser m1 = k a
                                      in m1 ls1)

happyGetToken :: (Lexeme Token -> Parser a) -> Parser a
happyGetToken k = Parser $ \s ->
  case nextToknes s of
    []     -> panic "happyGetToken" ["We run out of tokens.", "Missing TokEOF?"]
    t : ts -> let Parser m = k t
              in m PState { curToken = Just t, nextToknes = ts }

newtype ParseError = ParseError SourceRange
                      deriving Show

instance Exception ParseError

happyErrorAt :: SourcePos -> Parser a
happyErrorAt p = Parser (\_ -> Left (ParseError (range p)))

happyError :: Parser a
happyError = Parser $ \s ->
  Left $ ParseError
       $ case curToken s of
           Nothing ->
             case nextToknes s of
               [] -> panic "happyGetToken" ["We run out of tokens.", "Missing TokEOF?"]
               t : _ -> lexemeRange t
           Just t -> lexemeRange t

instance Pretty ParseError where
  ppPrec _ (ParseError x) =
    text (prettySourceRange x ++ ": Parse error.")

