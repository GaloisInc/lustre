-- | Reference:
-- http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
module Language.Lustre.AST
  ( module Language.Lustre.AST
  , SourceRange(..)
  , SourcePos(..)
  ) where

import Data.Text(Text)

import AlexTools(SourceRange(..), SourcePos(..), HasRange(..), (<->))

import Language.Lustre.Panic


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

data Expression = ERange !SourceRange !Expression
                | Var !Name
                | Lit !Literal

                | EOp1 Op1 Expression
                | EOp2 Expression Op2 Expression
                | EOpN OpN [Expression]

                | Tuple ![Expression]
                | Record ![Field]
                | Array ![Expression]

                | IfThenElse Expression Expression Expression
                | WithThenElse Expression Expression Expression
                  deriving Show
                -- XXX

data Literal    = Int Integer | Real Rational | Bool Bool
                  deriving Show

data Field      = Field Ident Expression
                  deriving Show


data Op1 = Not | Neg | Pre | Current | IntCast | RealCast
                  deriving Show

data Op2 = Fby | And | Or | Xor | Implies | Eq | Neq | Lt | Leq | Gt | Geq
         | Mul | IntDiv | Mod | Div | Add | Sub
         | When -- hm
                  deriving Show

data OpN = AtMostOne | Nor
                  deriving Show


instance HasRange Ident where
  range = identRange

instance HasRange Pragma where
  range = pragmaRange

instance HasRange Name where
  range nm =
    case nm of
      Unqual i -> range i
      Qual q i -> q <-> i

instance HasRange Field where
  range (Field x y) = x <-> y

-- Kind of...
instance HasRange Expression where
  range expr =
    case expr of
      ERange r _      -> r
      Var x           -> range x
      EOp2 e1 _ e2    -> e1 <-> e2

      Lit {}          -> nope "Lit"
      EOp1 {}         -> nope "EOp1"
      EOpN {}         -> nope "EOpN"
      Tuple {}        -> nope "Tuple"
      Record {}       -> nope "Record"
      Array {}        -> nope "Array"
      IfThenElse {}   -> nope "IfThenElse"
      WithThenElse {} -> nope "WithThenElse"
    where
    nope x = panic "range@Expresssion" [x]



