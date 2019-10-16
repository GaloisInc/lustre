-- | Reference:
-- http://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/doc/lv6-ref-man.pdf
module Language.Lustre.AST
  ( Program(..)

    -- * Packages

    {- | We don't support packages beyond parsing them. -}

  , PackDecl(..)
  , Package(..)
  , PackageProvides(..)


    -- * Top-Level Declarations
  , TopDecl(..)

    -- ** Types
  , TypeDecl(..)
  , TypeDef(..)
  , Type(..)
  , FieldType(..)
  , CType(..)
  , IClock(..)
  , CVar(..)

    -- ** Constants
  , ConstDef(..)

    -- ** Nodes
  , NodeDecl(..)
  , NodeInstDecl(..)
  , NodeProfile(..)
  , Safety(..)
  , NodeType(..)

  , InputBinder(..)
  , Binder(..)

  , NodeBody(..)
  , LocalDecl(..)
  , Equation(..)
  , AssertType(..)
  , LHS(..)
  , Selector(..)
  , ArraySlice(..)

  , Expression(..)
  , MergeCase(..)
  , ClockExpr(..)
  , NodeInst(..)



    -- ** Contracts
    -- {- | Support for contracts is incomplete. -}
  , Contract(..)
  , ContractItem(..)
  , ContractDecl(..)



  , eOp1
  , eOp2
  , eITE
  , eOpN

  , Callable(..)
  , PrimNode(..)
  , Iter(..)

  , StaticParam(..)
  , StaticArg(..)

  , Literal(..)

  , Field(..)


  , Op1(..)
  , Op2(..)
  , OpN(..)

  , exprRangeMaybe
  , typeRangeMaybe
  , argRangeMaybe
  , eqnRangeMaybe

  , HasRange(..)
  , SourceRange(..)
  , SourcePos(..)
  ) where

import Data.Maybe(fromMaybe)

import AlexTools(SourceRange(..), SourcePos(..), HasRange(..), (<->))

import Language.Lustre.Panic
import Language.Lustre.Name

-- | A Lustre program.  Currently we don't support packages beyond parsing.
data Program  = ProgramDecls [TopDecl]      -- ^ Some declarations
              | ProgramPacks [PackDecl]     -- ^ Some packages
                deriving Show

-- | A package declaration.  We can parse these, but not do anything with
-- them yet.
data PackDecl = PackDecl Package
              | PackInst Ident Ident [ (Ident, StaticArg) ]
                deriving Show

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
  | DeclareContract !ContractDecl
    deriving Show

-- | Declare a named type.
data TypeDecl = TypeDecl
  { typeName :: !Ident
  , typeDef  :: !(Maybe TypeDef)
    -- ^ Types with no definitions are abstract.
    -- We do not have good support for abstract types at the moment.
  } deriving Show



-- | A definition for a named type.
data TypeDef = IsType !Type             -- ^ A type alias.
             | IsEnum ![ Ident ]        -- ^ An enumeration type.
             | IsStruct ![ FieldType ]  -- ^ A record type.
              deriving Show

-- | The type of value or a constant.
data Type =
    NamedType Name                -- ^ A named type.  See 'TypeDef'.
  | ArrayType Type Expression
    -- ^ An array type.  The 'Expression' is for the size of the array.

  | IntType     -- ^ Type of integers.
  | RealType    -- ^ Type of real numbers.
  | BoolType    -- ^ Type of boolean values.

  | IntSubrange Expression Expression
    -- ^ An interval subset of the integers.  The 'Expression's are bounds.
    -- Their values are included in the interval.

  | TypeRange SourceRange Type
    -- ^ A type annotated with a source location.

    deriving Show


-- | The type of the field of a structure.
data FieldType  = FieldType
  { fieldName     :: Label              -- ^ The name of the field.
  , fieldType     :: Type               -- ^ The field's type.
  , fieldDefault  :: Maybe Expression
    -- ^ Optional default constant value, used if the field is omitted.
  } deriving Show


-- | Note: only one of the type or definition may be "Nothing".
data ConstDef = ConstDef
  { constName     :: Ident
  , constType     :: Maybe Type   -- ^ Optional type annotation.
  , constDef      :: Maybe Expression
    {- ^ Optional definition. If the definition is omitted, then the constant
         is abstract.  In that case, the type cannot be omitted.

         Note that at the moment we don't have good support for abstract
         constants. -}
  } deriving Show


data Contract = Contract
  { contractRange :: SourceRange
  , contractItems :: [ContractItem]
  } deriving Show

data ContractItem = GhostConst ConstDef
                  | GhostVar   Binder Expression
                  | Assume Label Expression
                  | Guarantee Label Expression
                  | Mode Ident [Expression] [Expression]
                  | Import Ident [Expression] [Expression]
                    deriving Show

data ContractDecl = ContractDecl
  { cdName     :: Ident
  , cdProfile  :: NodeProfile
  , cdItems    :: [ContractItem]
  , cdRange    :: SourceRange
  } deriving Show


-- | The declaration of a node.
data NodeDecl = NodeDecl
  { nodeSafety       :: Safety
  , nodeExtern       :: Bool
  , nodeType         :: NodeType
  , nodeName         :: Ident
  , nodeStaticInputs :: [StaticParam]
  , nodeProfile      :: NodeProfile
  , nodeContract     :: Maybe Contract
  , nodeDef          :: Maybe NodeBody
    -- Must be "Nothing" if "nodeExtern" is set to "True"
  , nodeRange        :: !SourceRange
  } deriving Show

-- | A named instantiation of a node with static parameters.
data NodeInstDecl = NodeInstDecl
  { nodeInstSafety       :: Safety
  , nodeInstType         :: NodeType
  , nodeInstName         :: Ident
  , nodeInstStaticInputs :: [StaticParam]
  , nodeInstProfile      :: Maybe NodeProfile
  , nodeInstDef          :: NodeInst
  } deriving Show


data NodeProfile = NodeProfile
  { nodeInputs    :: [InputBinder]
  , nodeOutputs   :: [Binder]
  } deriving Show


data Safety     = Safe        -- ^ No side effects
                | Unsafe      -- ^ May have side effects
                  deriving (Show,Eq)

data NodeType   = Node        -- ^ Nodes may have memory (e.g., use @pre@)
                | Function    -- ^ Functions do not have memory
                    deriving (Show, Eq)

{- | These are used to support the notation where constant parameters
are intermixed with normal parameters, rather then bing factored
out before. -}
data InputBinder = InputBinder Binder
                 | InputConst Ident Type
                   deriving Show

-- | Introduces a local variable (not constant).
data Binder = Binder
  { binderDefines :: Ident
  , binderType    :: CType
  } deriving Show


data NodeBody = NodeBody
  { nodeLocals  :: [LocalDecl]
  , nodeEqns    :: [Equation]
  } deriving Show

data LocalDecl  = LocalVar Binder
                | LocalConst ConstDef
                  deriving Show

data Equation   = Assert Label AssertType Expression     -- ^ Assuming this
                | Property Label Expression   -- ^ Prove this
                | IsMain SourceRange          -- ^ This is the main node,
                                              -- use it if nothing specified
                | IVC [Ident]
                | Realizable [Ident]
                | Define [LHS Expression] Expression
                  deriving Show

data AssertType = AssertPre -- failure of this assertion indicates an
                            -- error in the system.

                | AssertEnv -- failure of this assertion idicates an
                            -- unreachable system state.
                  deriving Show

data LHS e      = LVar Ident
                | LSelect (LHS e) (Selector e)
                  deriving (Show,Eq,Ord)

data Selector e = SelectField Label
                | SelectElement e
                | SelectSlice (ArraySlice e)
                  deriving (Show, Eq, Ord)

data ArraySlice e = ArraySlice
  { arrayStart :: e
  , arrayEnd   :: e
  , arrayStep  :: Maybe e
  } deriving (Show, Eq, Ord)


data Expression = ERange !SourceRange !Expression
                | Var !Name
                | Lit !Literal

                | Const Expression CType
                  {- ^ A use of a constant expression. These are introduced
                     by the type checker---the parser does not generate them.-}

                | Expression `When` ClockExpr

                | Tuple ![Expression]
                  -- ^ These are more like unboxed tuples in Haskell


                | Array ![Expression]
                | Select Expression (Selector Expression)
                | Struct Name [Field Expression]
                  -- ^ Create a new struct value.  'Name' is the struct type

                | UpdateStruct (Maybe Name) Expression [Field Expression]
                  {- ^ Update a struct.
                    The 'Name' is the struct type.
                    The expression is the struct being updated. -}

                | WithThenElse Expression Expression Expression
                  {- ^ Used for recursive definitions.
                    The decision is evaluated in an earlier phase (i.e.,
                    it is static), and then we get either the one stream or
                    the other (i.e., it is not done point-wise as
                    for if-then-else) -}

                | Merge Ident [MergeCase Expression]
                  {- ^ Merge different clocked values.  The branches are
                       clocked on different values for the ident. -}

                | Call NodeInst [Expression] IClock
                  {- ^ Call a function.
                      The clock expression allows for the node to
                      be called only when the clock is active. -}
                  deriving Show

-- | The first expression (the "pattern") should be a constant.
-- In fact, to check clocks, it is restricted to @true@, @false@, or a @Name@.
data MergeCase e = MergeCase Expression e
                    deriving Show

-- | The clock activates when the identifier has the given expression.
-- In the surface syntax, the expression is restricted to
-- @true@, @false@, or a @Name@ (e.g., for to use an enum).
-- However, allowing arbitrary expressions is more convenient for manipulating
-- already validated syntax (e.g., we can allow arbitrary values).
data ClockExpr  = WhenClock SourceRange Expression Ident
                  deriving Show


data NodeInst   = NodeInst Callable [StaticArg]
                  deriving Show

eOp1 :: SourceRange -> Op1 -> Expression -> Expression
eOp1 r op e = Call (NodeInst (CallPrim r (Op1 op)) []) [e] BaseClock

eOp2 :: SourceRange -> Op2 -> Expression -> Expression -> Expression
eOp2 r op e1 e2 = Call (NodeInst (CallPrim r (Op2 op)) []) [e1,e2] BaseClock

eITE :: SourceRange -> Expression -> Expression -> Expression -> Expression
eITE r e1 e2 e3 = Call (NodeInst (CallPrim r ITE) []) [e1,e2,e3] BaseClock

eOpN :: SourceRange -> OpN -> [Expression] -> Expression
eOpN r op es = Call (NodeInst (CallPrim r (OpN op)) []) es BaseClock

-- | Things that may be called
data Callable   = CallUser Name                   -- ^ A user-defined node
                | CallPrim SourceRange PrimNode   -- ^ A built-in node
                  deriving Show

data PrimNode   = Iter Iter
                | Op1 Op1
                | Op2 Op2
                | OpN OpN
                | ITE         -- (bool,a,a) -> a          -- (bool,a,a) -> a
                  deriving Show

-- | Built-in array iterators
data Iter       = IterFill        -- ^ Like @unfold@, but returns state;
                                  -- can generate multiple arrays at once

                | IterRed         -- ^ Like @fold@, but can fold multiple
                                  -- arrays at once

                | IterFillRed     -- ^ @fill@ and @red@ at the same time:
                                  -- the folding accumulator is the unfolding
                                  -- state

                | IterMap         -- ^ Like @fillred@ but with no accumulator

                | IterBoolRed     -- ^ Check if number of @True@s is within
                                  -- some bound
                  deriving Show

data StaticParam = TypeParam Ident
                 | ConstParam Ident Type
                 | NodeParam Safety NodeType Ident NodeProfile
                   deriving Show

data StaticArg  = TypeArg Type
                | ExprArg Expression
                | NodeArg NodeType NodeInst
                | ArgRange SourceRange StaticArg
                  deriving Show


data Literal    = Int Integer | Real Rational | Bool Bool
                  deriving (Show,Eq)

data Field e    = Field { fName :: Label, fValue :: e }
                  deriving Show

instance Functor Field where
  fmap f (Field l e) = Field l (f e)

instance Foldable Field where
  foldMap f (Field _ e) = f e

instance Traversable Field where
  traverse f (Field l e) = Field l <$> f e


data Op1 = Not          -- bool -> bool
         | Neg          -- Num a => a -> a
         | Pre          -- a -> a
         | Current      -- a -> a
         | IntCast      -- real -> int
         | FloorCast    -- real -> int
         | RealCast     -- int -> real
                  deriving (Show, Eq, Ord)

data Op2 = FbyArr       -- a -> a -> a
         | Fby          -- a -> a -> a
         | CurrentWith  -- like `current` but with a default value to use
                        -- at the start instead of nil
         | And          -- bool -> bool -> boo
         | Or           -- bool -> bool -> boo
         | Xor          -- bool -> bool -> boo
         | Implies      -- bool -> bool -> boo
         | Eq           -- a -> a -> bool
         | Neq          -- a -> a -> bool
         | Lt           -- Num a => a -> a -> bool
         | Leq          -- Num a => a -> a -> bool
         | Gt           -- Num a => a -> a -> bool
         | Geq          -- Num a => a -> a -> bool
         | Mul | Mod | Div | Add | Sub | Power    -- Num a => a -> a -> a
         | Replicate    -- a -> (n:Int) -> a^n
           -- XXX: the `n` is a constante so perhaps we should
           -- represent it as a static parametere.


         | Concat       -- a^M -> a^N -> a^(M+N)
           deriving (Show, Eq, Ord)

data OpN = AtMostOne | Nor
                  deriving (Show, Eq, Ord)


--------------------------------------------------------------------------------
-- Type checking

-- | The type of a non-constant expression.  We keep track of the clock,
-- and when the value may be updated.
data CType      = CType { cType :: Type, cClock :: IClock }
                  deriving Show

-- | A clock for a value.
data IClock =
    BaseClock
    {- ^ At the root node, this is the system's base clock.
         For other nodes, this refers to the clock of of the
         current node invocation.  See the 'Call' expression. -}

  | KnownClock ClockExpr
    -- ^ A specific clock expression.

  | ClockVar CVar
    -- ^ A placeholder for a clock that is being inferred.
    -- Used only during type-checking
    deriving Show

-- | A clock variable, used during type checking to infer the clock of
-- some expressions.
newtype CVar = CVar Int deriving (Eq,Ord,Show)



--------------------------------------------------------------------------------

instance HasRange e => HasRange (Field e) where
  range (Field x y) = x <-> y

instance HasRange ClockExpr where
  range (WhenClock r _ _) = r

-- | Get the source range associated with an expression, if any.
exprRangeMaybe :: Expression -> Maybe SourceRange
exprRangeMaybe expr =
  case expr of
    ERange r _      -> Just r
    Var x           -> Just (range x)
    e `When` c      -> Just (e  <-> c)

    Const e _        -> exprRangeMaybe e

    Lit {}          -> Nothing
    Tuple {}        -> Nothing
    Array {}        -> Nothing
    Select {}       -> Nothing
    WithThenElse {} -> Nothing
    Merge {}        -> Nothing
    Call {}         -> Nothing
    Struct {}       -> Nothing
    UpdateStruct {} -> Nothing


-- | Get the source range associated with a type, if any.
typeRangeMaybe :: Type -> Maybe SourceRange
typeRangeMaybe ty =
  case ty of
    TypeRange r _   -> Just r
    NamedType n     -> Just (range n)
    ArrayType {}    -> Nothing
    IntType {}      -> Nothing
    RealType {}     -> Nothing
    BoolType {}     -> Nothing
    IntSubrange {}  -> Nothing


-- | Get the source range of a static argument, if any.
argRangeMaybe :: StaticArg -> Maybe SourceRange
argRangeMaybe arg =
  case arg of
    ArgRange r _ -> Just r
    TypeArg t    -> typeRangeMaybe t
    ExprArg e    -> exprRangeMaybe e
    NodeArg {}   -> Nothing


-- | Get the source range of an equation, if any.
eqnRangeMaybe :: Equation -> Maybe SourceRange
eqnRangeMaybe eqn =
  case eqn of
    Assert _ _ e -> exprRangeMaybe e
    Property _ e -> exprRangeMaybe e
    IsMain r -> Just r
    IVC is ->
      case is of
        [] -> Nothing
        _  -> Just (range (head is) <-> range (last is))
    Realizable is ->
      case is of
        [] -> Nothing
        _  -> Just (range (head is) <-> range (last is))



    Define ls e ->
      case ls of
        [] -> exprRangeMaybe e
        l:_ -> Just $ case exprRangeMaybe e of
                        Nothing -> range l
                        Just r  -> range l <-> r

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

instance HasRange Callable where
  range c =
    case c of
      CallUser n -> range n
      CallPrim r _ -> r

instance HasRange Package where
  range = packageRange

instance HasRange e => HasRange (LHS e) where
  range lhs =
    case lhs of
      LVar i -> range i
      LSelect x y -> range x <-> range y


instance HasRange e => HasRange (Selector e) where
  range s =
    case s of
      SelectField f   -> range f
      SelectElement e -> range e
      SelectSlice a   -> range a

instance HasRange e => HasRange (ArraySlice e) where
  range a =
    range (arrayStart a) <-> range (fromMaybe (arrayEnd a) (arrayStep a))

instance HasRange StaticParam where
  range param =
    case param of
      TypeParam i       -> range i
      ConstParam i t    -> range i <-> range t
      NodeParam _ _ i _ -> range i

instance HasRange NodeDecl where
  range = nodeRange

instance HasRange Contract where
  range = contractRange

instance HasRange ContractDecl where
  range = cdRange


