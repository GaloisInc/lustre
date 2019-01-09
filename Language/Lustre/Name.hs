module Language.Lustre.Name where

import Data.Text(Text)
import qualified Data.Text as Text
import AlexTools(SourceRange(..), HasRange(..), SourcePos(..))

import Language.Lustre.Panic(panic)

data Ident = Ident
  { identText       :: !Text
  , identRange      :: !SourceRange
  , identPragmas    :: [Pragma]
  , identResolved   :: !(Maybe DefInfo)
  } deriving Show

withResolved :: (DefInfo -> a) -> Ident -> a
withResolved k i = case identResolved i of
                    Just info -> k info
                    Nothing -> panic "withResolved"
                                  [ "The identifier is not resolved."
                                  , "*** Name:  " ++ show (identText i)
                                  , "*** Range: " ++ show (identRange i)
                                  ]

-- | Access the unique identifier of a resolved identifier.
identUID :: Ident -> Int
identUID = withResolved rnUID

-- | Access the module, if any, of a resolved identifier.
identModule :: Ident -> Maybe ModName
identModule = withResolved rnModule

-- | Get information about what sort of thing this resolved identifier
-- refers to.
identThing :: Ident -> Thing
identThing = withResolved rnThing


data Pragma = Pragma
  { pragmaTextA     :: !Text
  , pragmaTextB     :: !Text
  , pragmaRange     :: !SourceRange
  } deriving Show

data Name =
    Unqual Ident
    -- ^ After name resolution, the 'identResolved' field of the
    -- identifier should always be filled in.

  | Qual SourceRange Text Text
    -- ^ Qualified name a produced in the parser, but should not
    -- be used after resolving names.
    deriving Show


-- | Make an ident with no known location.
-- This can be useful when looking up things in maps---only the 'Text'
-- matters.
identFromText :: Text -> Ident
identFromText txt = Ident { identText = txt
                          , identRange = dummy
                          , identPragmas = []
                          , identResolved = Nothing
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
  x == y = case (identResolved x, identResolved y) of
             (Just a, Just b)  -> a == b
             (Nothing,Nothing) -> identText x == identText y
             _                 -> False

instance Ord Ident where
  compare i j =
    case (identResolved i, identResolved j) of
      (Just x, Just y)   -> compare x y
      (Nothing, Nothing) -> compare (identText i) (identText j)
      (Nothing, Just _)  -> LT
      (Just _, Nothing)  -> GT



instance Eq Name where
  m == n = case (m,n) of
             (Unqual a, Unqual b)     -> a == b
             (Qual _ x y, Qual _ p q) -> (x,y) == (p,q)
             _                        -> False

instance Ord Name where
  compare m n = case (m,n) of
                  (Unqual x, Unqual y)     -> compare x y
                  (Unqual {}, _)           -> LT
                  (_, Unqual {})           -> GT
                  (Qual _ x y, Qual _ p q) -> compare (x,y) (p,q)


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


-- | Information about the definition of an identifier.
data DefInfo = DefInfo
  { rnUID     :: Int            -- ^ A unique identifier
  , rnModule  :: Maybe ModName  -- ^ Module where this is defined, if any
  , rnThing   :: Thing          -- ^ What are we
  } deriving Show

instance Eq DefInfo where
  x == y = rnUID x == rnUID y

instance Ord DefInfo where
  compare x y = compare (rnUID x) (rnUID y)


-- | The name of a module.
newtype ModName  = Module Text
  deriving (Eq,Ord,Show)


-- | What sorts of things can be defined
data Thing = AType | ANode | AContract | AConst | AVal
             deriving (Show,Eq,Ord)


-- | Various name spaces.
data NameSpace = NSType | NSNode | NSContract | NSVal
             deriving (Show,Eq,Ord)

-- | In what namespace do things live in.
thingNS :: Thing -> NameSpace
thingNS th =
  case th of
    AType     -> NSType
    ANode     -> NSNode
    AContract -> NSContract
    AVal      -> NSVal
    AConst    -> NSVal







