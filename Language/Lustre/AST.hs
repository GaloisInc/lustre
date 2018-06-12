-- | Reference:
-- http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
module Language.Lustre.AST
  ( module Language.Lustre.AST
  , SourceRange(..)
  , SourcePos(..)
  ) where

import Data.Text(Text)

import AlexTools(SourceRange(..), SourcePos(..))

data Ident = Ident
  { identText       :: !Text
  , identRange      :: !SourceRange
  } deriving Show

data Pragma = Pragma
  { pragmaText      :: !Text
  , pragmaRange     :: !SourceRange
  } deriving Show

-- | This is used for both packages and models.
data Package = Package
  { packageName     :: !Ident
  , packagePragmas  :: !Pragmas
  , packageUses     :: ![Ident]
  , packageParams   :: ![PackageParam]
  , packageProvides :: ![PackageParam]
  , packageBody     :: !(Maybe [TopDecl])
  } deriving Show

data PackageParam =
    PackageConst !Ident !Name !Pragmas
  | PackageType ![Ident]
  | PackageNode !(NodeDecl ())
    deriving Show


data TopDecl =
    DeclareType [Ident] Pragmas
  | DefineType Ident Type Pragmas
  | DeclareConst [Ident] Type Pragmas
  | DefineConst ConstDef
  | DeclareNode (NodeDecl ())
  | DefineNode  (NodeDecl NodeBody)
    deriving Show
  -- XXX: Model instances



type Pragmas    = [Pragma]



data Name       = Unqual Ident
                | Qual Ident Ident
                  deriving Show

data Type       = NamedType Name
                | RecrodType [ FieldType ]
                | ArrayType Type Expression
                | EnumType [ Ident ]
                  deriving Show

data FieldType  = FieldType { fieldName :: Ident, fieldType :: Type }
                    deriving Show



data ConstDef = ConstDef
  { constName     :: Ident
  , constType     :: Maybe Type
  , constDef      :: Expression
  , constPragmas  :: Pragmas
  } deriving Show

data NodeDecl def = NodeDecl
  { nodeUnsafe  :: Bool
  , nodeExtern  :: Bool
  , nodeType    :: NodeType
  , nodeInputs  :: [Binder]
  , nodeOutputs :: [Binder]
  , nodePragmas :: Pragmas
  , nodeDef     :: def
  } deriving Show

data NodeType   = Node | Function
                    deriving Show

data Binder = Binder
  { binderDefines :: [Ident]
  , binderType    :: Type
  , binderClock   :: Maybe Name
  , binderPragmas :: Pragmas
  } deriving Show

data NodeBody = NodeBody
  { nodeLocals  :: [LocalDecl]
  , nodeEqns    :: [Equation]
  } deriving Show

data LocalDecl  = LocalVar [Binder]
                | LocalConst [ConstDef]
                  deriving Show

data Equation   = Assert Expression Pragmas
                | Define [LHS] Expression Pragmas
                  deriving Show

data LHS        = LVar Name
                | LSelect LHS Selector
                  deriving Show

data Selector   = FieldSelector Ident
                | ArraySelector Expression (Maybe Expression)
                  deriving Show

data Expression = ERange SourceRange Expression
                | Var Name
                | Int Integer
                | Real Rational
                | Tuple [Expression]
                | Record Name [Field]
                | Array [Expression]
                  deriving Show
                -- XXX

data Field      = Field Ident Expression
                  deriving Show




