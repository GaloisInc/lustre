module Language.Lustre.Parser.Monad
  ( Parser
  , parseStartingAt
  , parse
  , happyGetToken
  , happyError
  , ParseError(..)
  ) where

import Control.Monad(liftM,ap)
import Control.Exception (Exception)
import Data.Text(Text)
import AlexTools(prevPos, startPos)

import Language.Lustre.Parser.Lexer
import Language.Lustre.Panic

newtype Parser a = Parser ([Lexeme Token] ->
                            Either ParseError (a, [Lexeme Token]))

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
  case m (lexer input) of
    Left err -> Left err
    Right (a,ls) ->
      case ls of
        []    -> Right a
        l : _ -> Left $ ParseError $ Just $ sourceFrom $ lexemeRange l
  where
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
happyGetToken k = Parser $ \ls ->
  case ls of
    []     -> panic "happyGetToken" ["We run out of tokens.", "Missing TokEOF?"]
    t : ts -> let Parser m = k t
              in m ts

newtype ParseError = ParseError (Maybe SourcePos) -- ^ Nothing means EOF
                      deriving Show

instance Exception ParseError


happyError :: Parser a
happyError = Parser $ \ls ->
  Left $ ParseError
       $ case ls of
           []    -> Nothing
           t : _ -> Just $ sourceFrom $ lexemeRange t



