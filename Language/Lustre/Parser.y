{
module Language.Lustre.Parser where

import Language.Lustre.Lexer
}


%tokentype { LexemeToken }

%token
  INT         { $$@Lexeme { lexemeToken = TokInteger  {} } }
  REAL        { $$@Lexeme { lexemeToken = TokRational {} } }

%name program program

%lexer { lexerP } { Located _ (Token EOF _) }
%monad { ParseM }

%nonassoc '=>'
%right '->'
%left     'where'

%%




{

-- More Haskell stuff
}
