module Language.Lustre.Name where

import Data.Text(Text)

import AlexTools(SourceRange(..), HasRange(..))

data Ident = Ident
  { identText       :: !Text
  , identRange      :: !SourceRange
  , identPragmas    :: [Pragma]
  } deriving Show

data Pragma = Pragma
  { pragmaTextA     :: !Text
  , pragmaTextB     :: !Text
  , pragmaRange     :: !SourceRange
  } deriving Show

data Name =
    Unqual Ident
  | Qual SourceRange Text Text
    deriving Show

--------------------------------------------------------------------------------

instance Eq Ident where
  x == y = identText x == identText y

instance Ord Ident where
  compare x y = compare (identText x) (identText y)



instance Eq Name where
  m == n = case (m,n) of
             (Unqual a, Unqual b)     -> a == b
             (Qual _ x y, Qual _ p q) -> (x,y) == (p,q)
             _                        -> False

instance Ord Name where
  compare m n = case (m,n) of
                  (Unqual x, Unqual y)     -> compare x y
                  (Unqual {}, _)           -> LT
                  (Qual _ x y, Qual _ p q) -> compare (x,y) (p,q)
                  (Qual {}, _)             -> GT


--------------------------------------------------------------------------------



instance HasRange Ident where
  range = identRange

instance HasRange Pragma where
  range = pragmaRange

instance HasRange Name where
  range nm =
    case nm of
      Unqual i   -> range i
      Qual r _ _ -> r


