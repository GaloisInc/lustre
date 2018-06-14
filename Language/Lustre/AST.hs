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
  | PackageNode !NodeDecl   -- ^ No body allowed
    deriving Show


data TopDecl =
    DeclareType  TypeDecl
  | DeclareConst ConstDef
  | DeclareNode  NodeDecl
    deriving Show
  -- XXX: Model instances

data TypeDecl = TypeDecl
  { typeName :: Ident
  , typeDef  :: TypeDef
  } deriving Show

data TypeDef = IsType Type
             | IsEnum [ Ident ]
             | IsStruct [ FieldType ]
             | IsAbstract
              deriving Show

type Pragmas    = [Pragma]

data Name =
    Unqual Ident
  | Qual Ident Ident
    deriving Show

data Type =
    NamedType Name
  | ArrayType Type Expression
  | IntType | RealType | BoolType
  | TypeRange SourceRange Type
    deriving Show


data FieldType  = FieldType
  { fieldName     :: Ident
  , fieldType     :: Type
  , fieldDefault  :: Maybe Expression
  } deriving Show


-- | Note: only one of the type or definition may be "Nothing".
data ConstDef = ConstDef
  { constName     :: Ident
  , constType     :: Maybe Type
  , constDef      :: Maybe Expression
  , constPragmas  :: Pragmas
  } deriving Show

data NodeDecl = NodeDecl
  { nodeUnsafe  :: Bool
  , nodeExtern  :: Bool
  , nodeType    :: NodeType
  , nodeName    :: Ident
  , nodeInputs  :: [Binder]
  , nodeOutputs :: [Binder]
  , nodePragmas :: Pragmas
  , nodeDef     :: Maybe NodeBody   -- Nothing if "nodeExtern" is set to "True"
  } deriving Show

data NodeType   = Node | Function
                    deriving Show

data Binder = Binder
  { binderDefines :: Ident
  , binderType    :: Type
  , binderClock   :: ClockExpr
  , binderPragmas :: Pragmas
  } deriving Show


data NodeBody = NodeBody
  { nodeLocals  :: [LocalDecl]
  , nodeEqns    :: [Equation]
  } deriving Show

data LocalDecl  = LocalVar Binder
                | LocalConst ConstDef
                  deriving Show

data Equation   = Assert Expression Pragmas
                | Define [LHS] Expression Pragmas
                  deriving Show

data LHS        = LVar Name
                | LSelect LHS Selector
                  deriving Show

data Selector   = SelectField Ident
                | SelectElement Expression
                | SelectSlice ArraySlice
                  deriving Show

data ArraySlice = ArraySlice
  { arrayStart :: Expression
  , arrayEnd   :: Expression
  , arrayStep  :: Maybe Expression
  } deriving Show

data Expression = ERange !SourceRange !Expression
                | Var !Name
                | Lit !Literal

                | EOp1 Op1 Expression
                | EOp2 Expression Op2 Expression
                | Expression `When` ClockExpr
                | EOpN OpN [Expression]

                | Tuple ![Expression]
                | Record ![Field]
                | Array ![Expression]
                | Select Expression Selector

                | IfThenElse Expression Expression Expression
                | WithThenElse Expression Expression Expression

                | CallPos NodeName [Expression]
                -- CallNamedArgs
                  deriving Show

data ClockExpr  = BaseClock SourceRange
                | WhenClock SourceRange ClockVal Ident
                  deriving Show

data ClockVal   = ClockIsTrue | ClockIsFalse | ClockIs Name
                  deriving Show

type StaticExpression = Expression -- XXX

data NodeName = NodeName Name [StaticExpression]
                deriving Show

data Literal    = Int Integer | Real Rational | Bool Bool
                  deriving Show

data Field      = Field Ident Expression
                  deriving Show


data Op1 = Not | Neg | Pre | Current | IntCast | RealCast
                  deriving Show

data Op2 = Fby | And | Or | Xor | Implies | Eq | Neq | Lt | Leq | Gt | Geq
         | Mul | IntDiv | Mod | Div | Add | Sub
         | Replicate | Concat
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

instance HasRange ClockExpr where
  range e =
    case e of
      BaseClock r -> r
      WhenClock r _ _ -> r

exprRangeMaybe :: Expression -> Maybe SourceRange
exprRangeMaybe expr =
  case expr of
    ERange r _      -> Just r
    Var x           -> Just (range x)
    EOp2 e1 _ e2    -> Just (e1 <-> e2)
    e `When` c      -> Just (e  <-> c)

    Lit {}          -> Nothing
    EOp1 {}         -> Nothing
    EOpN {}         -> Nothing
    Tuple {}        -> Nothing
    Record {}       -> Nothing
    Array {}        -> Nothing
    Select {}       -> Nothing
    IfThenElse {}   -> Nothing
    WithThenElse {} -> Nothing
    CallPos {}      -> Nothing

typeRangeMaybe :: Type -> Maybe SourceRange
typeRangeMaybe ty =
  case ty of
    TypeRange r _ -> Just r
    NamedType n   -> Just (range n)
    ArrayType {}  -> Nothing
    IntType {}    -> Nothing
    RealType {}   -> Nothing
    BoolType {}   -> Nothing

-- | Note that this is a partial function: it will panic if the
-- expression does not have an exact location.
instance HasRange Type where
  range ty = case typeRangeMaybe ty of
               Just r -> r
               Nothing -> panic "range@Type" [ "Type has no location"
                                             , show ty ]

-- | Note that this is a partial function: it will panic if the
-- expression does not have an exact location.
instance HasRange Expression where
  range expr =
    case exprRangeMaybe expr of
      Just r -> r
      Nothing -> panic "range@Expression" [ "Expression has no location"
                                          , show expr ]

