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
  }

data Pragma = Pragma
  { pragmaText      :: !Text
  , pragmaRange     :: !SourceRange
  }

-- | This is used for both packages and models.
data Package = Package
  { packageName     :: !Ident
  , packagePragmas  :: !Pragmas
  , packageUses     :: ![Ident]
  , packageParams   :: ![PackageParam]
  , packageProvides :: ![PackageParam]
  , packageBody     :: !(Maybe [TopDecl])
  }

data PackageParam =
    PackageConst !Ident !Name !Pragmas
  | PackageType ![Ident]
  | PackageNode !(NodeDecl ())


data TopDecl =
    DeclareType [Ident] Pragmas
  | DefineType Ident Type Pragmas
  | DeclareConst [Ident] Type Pragmas
  | DefineConst ConstDef
  | DeclareNode (NodeDecl ())
  | DefineNode  (NodeDecl NodeBody)
  -- XXX: Model instances



type Pragmas    = [Pragma]



data Name       = Unqual Ident
                | Qual Ident Ident

data Type       = NamedType Name
                | RecrodType [ FieldType ]
                | ArrayType Type Expression
                | EnumType [ Ident ]

data FieldType  = FieldType { fieldName :: Ident, fieldType :: Type }



data ConstDef = ConstDef
  { constName     :: Ident
  , constType     :: Maybe Type
  , constDef      :: Expression
  , constPragmas  :: Pragmas
  }

data NodeDecl def = NodeDecl
  { nodeUnsafe  :: Bool
  , nodeExtern  :: Bool
  , nodeType    :: NodeType
  , nodeInputs  :: [Binder]
  , nodeOutputs :: [Binder]
  , nodePragmas :: Pragmas
  , nodeDef     :: def
  }

data NodeType   = Node | Function

data Binder = Binder
  { binderDefines :: [Ident]
  , binderType    :: Type
  , binderClock   :: Maybe Name
  , binderPragmas :: Pragmas
  }

data NodeBody = NodeBody
  { nodeLocals  :: [LocalDecl]
  , nodeEqns    :: [Equation]
  }

data LocalDecl  = LocalVar [Binder]
                | LocalConst [ConstDef]

data Equation   = Assert Expression Pragmas
                | Define [LHS] Expression Pragmas

data LHS        = LVar Name
                | LSelect LHS Selector

data Selector   = FieldSelector Ident
                | ArraySelector Expression (Maybe Expression)

data Expression = ERange SourceRange Expression
                | Var Name
                | Lit Literal
                | MultiExpr [Expression]
                | Record Name [Field]
                | Array [Expression]
                -- XXX

data Field      = Field Ident Expression

data Literal    = IntLit  Integer
                | RealLit Rational



