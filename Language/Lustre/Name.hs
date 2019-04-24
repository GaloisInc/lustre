module Language.Lustre.Name where

import Data.Text(Text)
import AlexTools(SourceRange(..), HasRange(..))

import Language.Lustre.Panic(panic)

{- | Just a textual name.  Used to remember the user specified names of
things, as well as for things that are not quite names (e.g., field
labels)  -}
data Label = Label
  { labText   :: !Text
    -- ^ The label's text.

  , labRange  :: !SourceRange
    -- ^ The location of the lable in the source program.
  } deriving Show


{- | The type of unqualified names
Used when we define things and at some use sites that can only refer to
locally defined things. -}
data Ident = Ident
  { identLabel    :: !Label
  , identResolved :: !(Maybe OrigName)
  } deriving Show

-- | The text associates with an identifier.
identText :: Ident -> Text
identText = labText . identLabel

-- | The location of the idnetifier in the source program.
identRange :: Ident -> SourceRange
identRange = labRange . identLabel

-- | Do something with a resolve idnetifier.
-- Panics if the identifier is not resolved.
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


-- | A possibly qualified name.  Used at use sites where qualifier might be
-- OK. Mostly used to refer to types and constants in other modules.
data Name =
    Unqual Ident
    -- ^ After name resolution, the 'identResolved' field of the
    -- identifier should always be filled in.

  | Qual ModName Ident
    -- ^ Qualified name. Produced in the parser. Should not appear
    -- after name resolution, where all names should be unqualified resolved
    -- identifiers.
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

--------------------------------------------------------------------------------


-- | Comapred by text.
instance Eq Label where
  x == y = labText x == labText y

-- | Comapred by text.
instance Ord Label where
  compare x y = compare (labText x) (labText y)



-- | Comapred by original name, if available, or by text otherwise.
-- Resolved and unresolved names are different.
instance Eq Ident where
  x == y = case (identResolved x, identResolved y) of
             (Just a, Just b)  -> a == b
             (Nothing,Nothing) -> identText x == identText y
             _                 -> False

-- | Same as 'Eq'
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







