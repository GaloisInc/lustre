module Language.Lustre.Name where

import Data.Text(Text)
import AlexTools(SourceRange(..), HasRange(..))

import Language.Lustre.Panic(panic)

data Label = Label
  { labText   :: !Text
  , labRange  :: !SourceRange
  } deriving Show

data Ident = Ident
  { identLabel    :: !Label
  , identResolved :: !(Maybe OrigName)
  } deriving Show

identText :: Ident -> Text
identText = labText . identLabel

identRange :: Ident -> SourceRange
identRange = labRange . identLabel

withResolved :: (OrigName -> a) -> Ident -> a
withResolved k i = case identResolved i of
                    Just info -> k info
                    Nothing -> panic "withResolved"
                                  [ "The identifier is not resolved."
                                  , "*** Name:  " ++ show (identText i)
                                  , "*** Range: " ++ show (identRange i)
                                  ]

-- | Access the definition site for the given resolved identifier.
identOrigName :: Ident -> OrigName
identOrigName = withResolved id

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


data Name =
    Unqual Ident
    -- ^ After name resolution, the 'identResolved' field of the
    -- identifier should always be filled in.

  | Qual ModName Ident
    -- ^ Qualified name a produced in the parser, but should not
    -- be used after resolving names.
    deriving Show


-- | Get the original name of a resolved name.
nameOrigName :: Name -> OrigName
nameOrigName nm =
  case nm of
    Unqual i -> identOrigName i
    Qual {}  -> panic "nameOrigName"
                  [ "Unexpected qualified name:"
                  , "*** Name: " ++ show nm
                  ]

labelFromText :: SourceRange -> Text -> Label
labelFromText r t = Label { labText = t, labRange = r }

-- | Make an ident with no known location.
-- This can be useful when looking up things in maps---only the 'Text'
-- matters.
identFromText :: SourceRange -> Text -> Ident
identFromText rng txt = Ident { identLabel    = labelFromText rng txt
                              , identResolved = Nothing
                              }
--------------------------------------------------------------------------------


instance Eq Label where
  x == y = labText x == labText y

instance Ord Label where
  compare x y = compare (labText x) (labText y)



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

      -- This are arbitrary, and somehwat questionable.
      -- Perhaps we should panic instead?
      (Nothing, Just _)  -> LT
      (Just _, Nothing)  -> GT



instance Eq Name where
  m == n = case (m,n) of
             (Unqual a, Unqual b) -> a == b
             (Qual x y, Qual p q) -> (x,y) == (p,q)
             _                    -> False

instance Ord Name where
  compare m n = case (m,n) of
                  (Unqual x, Unqual y)  -> compare x y
                  (Unqual {}, _)        -> LT
                  (_, Unqual {})        -> GT
                  (Qual x y, Qual p q)  -> compare (x,y) (p,q)


--------------------------------------------------------------------------------


instance HasRange Label where
  range = labRange

instance HasRange Ident where
  range = identRange

instance HasRange Name where
  range nm =
    case nm of
      Unqual i -> range i
      Qual _ i -> range i


-- | Information about the definition of an identifier.
data OrigName = OrigName
  { rnUID     :: !Int             -- ^ A unique identifier
  , rnModule  :: !(Maybe ModName) -- ^ Module where this is defined, if any
  , rnIdent   :: !Ident           -- ^ Original (unresolved) identifier at
                                  -- definition site.  Useful for location,
                                  -- pragmas, etc.
  , rnThing   :: !Thing           -- ^ What are we
  } deriving Show

origNameToIdent :: OrigName -> Ident
origNameToIdent d = (rnIdent d) { identResolved = Just d }

origNameToName :: OrigName -> Name
origNameToName = Unqual . origNameToIdent

-- | The textual name of an original name, without module.
origNameTextName :: OrigName -> Text
origNameTextName n = identText (rnIdent n)

instance HasRange OrigName where
  range = range . rnIdent

instance Eq OrigName where
  x == y = rnUID x == rnUID y

instance Ord OrigName where
  compare x y = compare (rnUID x) (rnUID y)


-- | The name of a module.
newtype ModName = Module Text
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







