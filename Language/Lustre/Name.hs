module Language.Lustre.Name where

import Data.Text(Text)
import qualified Data.Text as Text
import AlexTools(SourceRange(..), HasRange(..), SourcePos(..))

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


-- | Make an ident with no known location.
-- This can be useful when looking up things in maps---only the 'Text'
-- matters.
identFromText :: Text -> Ident
identFromText txt = Ident { identText = txt
                          , identRange = dummy
                          , identPragmas = []
                          }
  where
  dummy    = SourceRange { sourceFrom = dummyPos, sourceTo = dummyPos }
  dummyPos = SourcePos { sourceIndex  = -1
                       , sourceLine   = -1
                       , sourceColumn = -1
                       , sourceFile   = Text.pack ""
                       }

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



-- | A defined thing.
data ResolvedName = ResolvedName
  { rnUID     :: Int            -- ^ A unique identifier
  , rnIdent   :: Ident          -- ^ Our name
  , rnModule  :: Maybe ModName  -- ^ Module where this is defined, if any
  , rnThing   :: Thing          -- ^ What are we
  }

instance HasRange ResolvedName where
  range = range . rnIdent

instance Eq ResolvedName where
  x == y = rnUID x == rnUID y

instance Ord ResolvedName where
  compare x y = compare (rnUID x) (rnUID y)


-- | The name of a module.
newtype ModName  = Module Text
  deriving (Eq,Ord,Show)


-- | What sorts of things can be defined
data Thing = AType | ANode | AContract | AConst | AVal
             deriving (Show,Eq,Ord)


data NameSpace = NSType | NSNode | NSContract | NSVal
             deriving (Show,Eq,Ord)

thingNS :: Thing -> NameSpace
thingNS th =
  case th of
    AType     -> NSType
    ANode     -> NSNode
    AContract -> NSContract
    AVal      -> NSVal
    AConst    -> NSVal







