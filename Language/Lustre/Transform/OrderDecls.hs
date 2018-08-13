module Language.Lustre.Transform.OrderDecls (orderTopDecls) where

import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)

import Language.Lustre.AST


orderTopDecls :: [TopDecl] -> [SCC TopDecl]
orderTopDecls ds = stronglyConnComp graph
  where
  getRep x = Map.findWithDefault x x repMap

  (repMap, graph) = foldr addRep (Map.empty,[]) ds

  addRep d (mp, gs) =
    case Set.minView (defines d) of
      Nothing -> (mp,gs)    -- shouldn't happen?
      Just (a,rest) ->
        ( foldr (\x -> Map.insert x a) mp rest
        , (d, a, map getRep (Set.toList (uses d))) : gs
        )



--------------------------------------------------------------------------------

data NS = T | V deriving (Show,Eq,Ord)

type Names = Set (NS,Name)

without :: Names -> Names -> Names
without = Set.difference

aType :: Name -> Names
aType x = Set.singleton (T,x)

aVal :: Name -> Names
aVal x = Set.singleton (V,x)

--------------------------------------------------------------------------------

class Uses t where
  uses :: t -> Names

class Defines t where
  defines :: t -> Names


instance Uses a => Uses [a] where
  uses = mconcat . map uses

instance Defines a => Defines [a] where
  defines = mconcat . map defines

instance Uses a => Uses (Maybe a) where
  uses = maybe mempty uses

instance (Uses a, Uses b) => Uses (a,b) where
  uses (x,y) = mappend (uses x) (uses y)

instance Uses TopDecl where
  uses ts =
    case ts of
      DeclareType td -> uses td
      DeclareConst cd -> uses cd
      DeclareNode nd -> uses nd
      DeclareNodeInst nid -> uses nid

instance Defines TopDecl where
  defines ts =
    case ts of
      DeclareType td -> defines td
      DeclareConst cd -> defines cd
      DeclareNode nd -> defines nd
      DeclareNodeInst nid -> defines nid




instance Uses TypeDecl where
  uses = uses . typeDef

instance Defines TypeDecl where
  defines td = aType (Unqual (typeName td)) <> defines (typeDef td)


instance Uses TypeDef where
  uses td =
    case td of
      IsType t -> uses t
      IsEnum _ -> mempty
      IsStruct fs -> uses fs
      IsAbstract -> mempty

instance Defines TypeDef where
  defines td =
    case td of
      IsType _ -> mempty
      IsEnum xs -> mconcat (map (aVal . Unqual) xs)
      IsStruct _ -> mempty
      IsAbstract -> mempty



instance Uses FieldType where
  uses t = uses (fieldType t, fieldDefault t)

instance Uses Field where
  uses (Field _ e) = uses e

instance Uses Type where
  uses ty =
    case ty of
      NamedType t -> aType t
      ArrayType t e -> uses (t,e)
      IntType -> mempty
      RealType -> mempty
      BoolType -> mempty
      TypeRange _ t -> uses t


instance Uses ConstDef where
  uses cd = uses (constType cd, constDef cd)

instance Defines ConstDef where
  defines = aVal . Unqual . constName

instance Uses StaticParam where
  uses sp =
    case sp of
      TypeParam _ -> mempty
      ConstParam _ t -> uses t
      NodeParam _ _ _ p -> uses p

instance Defines StaticParam where
  defines sp =
    case sp of
      TypeParam t       -> aType (Unqual t)
      ConstParam c _    -> aVal (Unqual c)
      NodeParam _ _ i _ -> aVal (Unqual i)

instance Uses NodeProfile where
  uses np = uses (nodeInputs np, nodeOutputs np)

instance Defines NodeProfile where
  defines = defines . nodeInputs

instance Uses Binder where
  uses b = uses (binderType b, binderClock b)

instance Defines Binder where
  defines = aVal . Unqual . binderDefines


instance Uses StaticArg where
  uses sa =
    case sa of
      TypeArg t     -> uses t
      ExprArg e     -> uses e
      NodeArg _ ni  -> uses ni
      Op1Arg _      -> mempty
      Op2Arg _      -> mempty
      OpIf          -> mempty
      ArgRange _ a  -> uses a

instance Uses NodeInstDecl where
  uses nid = uses (nodeInstStaticInputs nid,
                            (nodeInstProfile nid, nodeInstDef nid))


instance Defines NodeInstDecl where
  defines nd = aVal (Unqual (nodeInstName nd))

instance Uses NodeInst where
  uses (NodeInst x as) = aVal x <> uses as

instance Uses Expression where
  uses expr =
    case expr of
      ERange _ e -> uses e
      Var x -> aVal x
      Lit _ -> mempty
      EOp1 _ e -> uses e
      EOp2 e1 _ e2 -> uses (e1,e2)
      e1 `When` e2 -> uses (e1,e2)
      EOpN _ es -> uses es
      Tuple es -> uses es
      Array es -> uses es
      Select e s -> uses (e,s)
      Struct x y fs -> mconcat [ aType x, maybe mempty aVal y, uses fs ]
      IfThenElse e1 e2 e3 -> uses (e1, (e2,e3))
      WithThenElse e1 e2 e3 -> uses (e1, (e2,e3))
      Merge x es -> aVal (Unqual x) <> uses es
      CallPos f es -> uses (f,es)

instance Uses MergeCase where
  uses (MergeCase c v) = uses (c,v)

instance Uses ClockVal where
  uses cv =
    case cv of
      ClockIsTrue  -> mempty
      ClockIsFalse -> mempty
      ClockIs x    -> aVal x

instance Uses ClockExpr where
  uses (WhenClock _ cv i) = uses cv `mappend` aVal (Unqual i)


instance Uses NodeDecl where
  uses x = uses (nodeStaticInputs x) <>
           ((uses (nodeProfile x) <>
              (uses (nodeDef x) `without` defines (nodeProfile x)))
           `without` defines (nodeStaticInputs x))

instance Defines NodeDecl where
  defines nd = aVal (Unqual (nodeName nd))

instance Uses NodeBody where
  uses x = uses (nodeLocals x, nodeEqns x)
              `without` defines (nodeLocals x)

instance Uses LocalDecl where
  uses ld =
    case ld of
      LocalVar b -> uses b
      LocalConst c -> uses c

instance Defines LocalDecl where
  defines ld =
    case ld of
      LocalVar b -> defines b
      LocalConst b -> defines b

instance Uses Equation where
  uses eqn =
    case eqn of
      Assert e -> uses e
      Define lhs e -> uses (lhs,e)

instance Uses e => Uses (LHS e) where
  uses lhs =
    case lhs of
      LVar _ -> mempty
      LSelect x e -> uses (x,e)

instance Uses e => Uses (Selector e) where
  uses sel =
    case sel of
      SelectField _ -> mempty
      SelectElement e -> uses e
      SelectSlice e -> uses e

instance Uses e => Uses (ArraySlice e) where
  uses as = uses (arrayStart as, (arrayEnd as, arrayStep as))



