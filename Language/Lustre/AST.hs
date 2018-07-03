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

data Program  = ProgramDecls [TopDecl]
              | ProgramPacks [PackDecl]
                deriving Show

data PackDecl = PackDecl Package
              | PackInst Ident Ident [ (Ident, StaticArg) ]
                deriving Show

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

-- | This is used for both packages and models.
data Package = Package
  { packageName     :: !Ident
  , packageUses     :: ![Ident]
  , packageParams   :: ![StaticParam]   -- ^ Empty list for pacakges
  , packageProvides :: ![PackageProvides]
  , packageBody     :: ![TopDecl]
  , packageRange    :: !SourceRange
  } deriving Show

data PackageProvides =
    ProvidesConst !Ident !Type !(Maybe Expression)
  | ProvidesNode  !NodeDecl
  | ProvidesType  !TypeDecl
    deriving Show


data TopDecl =
    DeclareType     !TypeDecl
  | DeclareConst    !ConstDef
  | DeclareNode     !NodeDecl
  | DeclareNodeInst !NodeInstDecl
    deriving Show

data TypeDecl = TypeDecl
  { typeName :: !Ident
  , typeDef  :: !TypeDef
  } deriving Show

data TypeDef = IsType !Type
             | IsEnum ![ Ident ]
             | IsStruct ![ FieldType ]
             | IsAbstract
              deriving Show

type Pragmas    = [Pragma]

data Name =
    Unqual Ident
  | Qual SourceRange Text Text
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
  } deriving Show

data Safety = Safe | Unsafe
              deriving Show

data NodeDecl = NodeDecl
  { nodeSafety       :: Safety
  , nodeExtern       :: Bool
  , nodeType         :: NodeType
  , nodeName         :: Ident
  , nodeStaticInputs :: [StaticParam]
  , nodeProfile      :: NodeProfile
  , nodeDef          :: Maybe NodeBody
    -- Must be "Nothing" if "nodeExtern" is set to "True"
  } deriving Show

data NodeInstDecl = NodeInstDecl
  { nodeInstSafety       :: Safety
  , nodeInstType         :: NodeType
  , nodeInstName         :: Ident
  , nodeInstStaticInputs :: [StaticParam]
  , nodeInstProfile      :: Maybe NodeProfile
  , nodeInstDef          :: NodeInst
  } deriving Show

data NodeProfile = NodeProfile
  { nodeInputs  :: [Binder]
  , nodeOutputs :: [Binder]
  } deriving Show

data NodeType   = Node | Function
                    deriving Show

data Binder = Binder
  { binderDefines :: Ident
  , binderType    :: Type
  , binderClock   :: ClockExpr
  } deriving Show


data NodeBody = NodeBody
  { nodeLocals  :: [LocalDecl]
  , nodeEqns    :: [Equation]
  } deriving Show

data LocalDecl  = LocalVar Binder
                | LocalConst ConstDef
                  deriving Show

data Equation   = Assert Expression
                | Define [LHS] Expression
                  deriving Show

data LHS        = LVar Ident
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
                  -- ^ Recursive definition

                | Merge Ident [MergeCase]

                | CallPos NodeInst [Expression]
                | CallNamed Name (Maybe Name) [Field]
                  -- ^ The 'Maybe' parameter corresponds to @with@
                  -- and is used for updating structs.
                  deriving Show

data MergeCase  = MergeCase ClockVal Expression
                  deriving Show

data ClockExpr  = BaseClock SourceRange
                | WhenClock SourceRange ClockVal Ident
                  deriving Show

data ClockVal   = ClockIsTrue   -- ^ Like @ClockIs true@
                | ClockIsFalse  -- ^ Like @ClockIs false@
                | ClockIs Name  -- ^ Activates when the clock variable gets
                                -- this value.  In this way non-boolean types
                                -- can be used for clocks.
                  deriving Show

data NodeInst   = NodeInst Name [StaticArg]
                  deriving Show

data StaticParam = TypeParam Ident
                 | ConstParam Ident Type
                 | NodeParam Safety NodeType Ident [Binder] [Binder]
                   deriving Show

data StaticArg  = TypeArg Type
                | ExprArg Expression
                | NodeArg NodeType NodeInst
                | Op1Arg Op1
                | Op2Arg Op2
                | OpIf
                | ArgRange SourceRange StaticArg
                  deriving Show


data Literal    = Int Integer | Real Rational | Bool Bool
                  deriving Show

data Field      = Field Ident Expression
                  deriving Show


data Op1 = Not | Neg | Pre | Current | IntCast | RealCast
                  deriving Show

data Op2 = Fby | And | Or | Xor | Implies | Eq | Neq | Lt | Leq | Gt | Geq
         | Mul | IntDiv | Mod | Div | Add | Sub | Power
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
      Unqual i   -> range i
      Qual r _ _ -> r

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
    Merge {}        -> Nothing
    CallPos {}      -> Nothing
    CallNamed {}    -> Nothing

typeRangeMaybe :: Type -> Maybe SourceRange
typeRangeMaybe ty =
  case ty of
    TypeRange r _ -> Just r
    NamedType n   -> Just (range n)
    ArrayType {}  -> Nothing
    IntType {}    -> Nothing
    RealType {}   -> Nothing
    BoolType {}   -> Nothing

argRangeMaybe :: StaticArg -> Maybe SourceRange
argRangeMaybe arg =
  case arg of
    ArgRange r _ -> Just r
    TypeArg t    -> typeRangeMaybe t
    ExprArg e    -> exprRangeMaybe e
    NodeArg {}   -> Nothing
    Op1Arg {}    -> Nothing
    Op2Arg {}    -> Nothing
    OpIf {}      -> Nothing

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

-- | Note that this is a partial function: it will panic if the
-- expression does not have an exact location.
instance HasRange StaticArg where
  range arg =
    case argRangeMaybe arg of
      Just r -> r
      Nothing -> panic "range@StaticArg" [ "Static argument has no location"
                                         , show arg ]

instance HasRange NodeInst where
  range (NodeInst x _) = range x  -- or args?

instance HasRange Package where
  range = packageRange


