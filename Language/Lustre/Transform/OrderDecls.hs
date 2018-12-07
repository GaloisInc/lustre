{-# Language ImplicitParams #-}
module Language.Lustre.Transform.OrderDecls (orderTopDecls) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup ( (<>) )
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)

import Language.Lustre.AST
import Language.Lustre.Pretty(showPP)
import Language.Lustre.Panic(panic)


orderTopDecls :: [TopDecl] -> [TopDecl]
orderTopDecls ds = concatMap orderRec (stronglyConnComp graph)
  where
  getRep x = Map.findWithDefault x x repMap

  (repMap, graph) = foldr addRep (Map.empty,[]) ds

  addRep d (mp, gs) =
    let ?contractInfo = contractInfo Map.empty (orderContracts ds)
    in
    case Set.minView (defines d) of
      Nothing -> (mp,gs)    -- shouldn't happen?
      Just (a,rest) ->
        ( foldr (\x -> Map.insert x a) mp rest
        , (d, a, map getRep (Set.toList (uses d))) : gs
        )

orderContracts :: [TopDecl] -> [ContractDecl]
orderContracts ds = map check (stronglyConnComp graph)
  where
  deps c        = [ d | Import d _ _ <- cdItems c ]
  graph         = [ (c,cdName c, deps c) | DeclareContract c <- ds ]

  check s = case s of
              AcyclicSCC x -> x
              CyclicSCC xs -> panic "orderContracts"
                                [ "Recursive top-level constracts:"
                                , "*** " ++ unwords (map (showPP . cdName) xs)
                                ]

contractInfo :: ContractInfo -> [ContractDecl] -> ContractInfo
contractInfo = foldl addDefs
  where
  addDefs done c = let ?contractInfo = done
                   in Map.insert (Unqual (cdName c)) (definesContract c) done



-- | Place declarations with no static parameters after declarations with
-- static parameters.  We assume that the inputs were already validated,
-- so this does not do proper error checking.
orderRec :: SCC TopDecl -> [TopDecl]
orderRec comp =
  case comp of
    AcyclicSCC x -> [x]
    CyclicSCC xs -> case break noParam xs of
                      (as,b:bs) -> as ++ bs ++ [b]
                      _         -> xs
      where
      noParam td =
        case td of
          DeclareNode nd      -> null (nodeStaticInputs nd)
          DeclareNodeInst nid -> null (nodeInstStaticInputs nid)
          _                   -> False


--------------------------------------------------------------------------------

data NS = TypeNS | ValNS | ContractNS deriving (Show,Eq,Ord)

type Names = Set (NS,Name)

without :: Names -> Names -> Names
without = Set.difference

aType :: Name -> Names
aType x = Set.singleton (TypeNS,x)

aVal :: Name -> Names
aVal x = Set.singleton (ValNS,x)

aContract :: Name -> Names
aContract x = Set.singleton (ContractNS,x)

--------------------------------------------------------------------------------

-- | Ghost variables introduced by contracts
type ContractInfo = Map Name Names

class Uses t where
  uses :: (?contractInfo :: ContractInfo) => t -> Names

class Defines t where
  defines :: t -> Names


instance Uses a => Uses [a] where
  uses = mconcat . map uses

instance Defines a => Defines [a] where
  defines = mconcat . map defines

instance Uses a => Uses (Maybe a) where
  uses = maybe mempty uses

instance Defines a => Defines (Maybe a) where
  defines = maybe mempty defines

instance (Uses a, Uses b) => Uses (a,b) where
  uses (x,y) = mappend (uses x) (uses y)

instance Uses TopDecl where
  uses ts =
    case ts of
      DeclareType td -> uses td
      DeclareConst cd -> uses cd
      DeclareNode nd -> uses nd
      DeclareNodeInst nid -> uses nid
      DeclareContract cd -> uses cd

instance Defines TopDecl where
  defines ts =
    case ts of
      DeclareType td -> defines td
      DeclareConst cd -> defines cd
      DeclareNode nd -> defines nd
      DeclareNodeInst nid -> defines nid
      DeclareContract cd -> defines cd




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

instance Defines TypeDef where
  defines td =
    case td of
      IsType _ -> mempty
      IsEnum xs -> mconcat (map (aVal . Unqual) xs)
      IsStruct _ -> mempty


instance Uses FieldType where
  uses t = uses (fieldType t, fieldDefault t)

instance Uses e => Uses (Field e) where
  uses (Field _ e) = uses e

instance Uses Type where
  uses ty =
    case ty of
      NamedType t -> aType t
      ArrayType t e -> uses (t,e)
      IntSubrange e1 e2 -> uses (e1,e2)
      IntType -> mempty
      RealType -> mempty
      BoolType -> mempty
      TVar x -> panic "uses@Type" [ "Unexpected type variable"
                                  , "*** Tvar: " ++ showPP x ]
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

instance Uses InputBinder where
  uses ib =
    case ib of
      InputBinder b  -> uses b
      InputConst _ t -> uses t

instance Defines InputBinder where
  defines ib =
    case ib of
      InputBinder b -> defines b
      InputConst c _ -> aVal (Unqual c)

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
      ArgRange _ a  -> uses a

instance Uses NodeInstDecl where
  uses nid = uses (nodeInstStaticInputs nid,
                            (nodeInstProfile nid, nodeInstDef nid))


instance Defines NodeInstDecl where
  defines nd = aVal (Unqual (nodeInstName nd))

instance Uses NodeInst where
  uses (NodeInst x as) = uses (x,as)

instance Uses Callable where
  uses c =
    case c of
      CallUser n  -> aVal n
      CallPrim {} -> mempty

instance Uses Expression where
  uses expr =
    case expr of
      ERange _ e -> uses e
      Var x -> aVal x
      Lit _ -> mempty
      e1 `When` e2 -> uses (e1,e2)
      Tuple es -> uses es
      Array es -> uses es
      Select e s -> uses (e,s)
      Struct x fs -> mconcat [ aType x, uses fs ]
      UpdateStruct x y fs -> mconcat [ aType x, aVal y, uses fs ]
      WithThenElse e1 e2 e3 -> uses (e1, (e2,e3))
      Merge x es -> aVal (Unqual x) <> uses es
      Call f es -> uses (f,es)

instance Uses e => Uses (MergeCase e) where
  uses (MergeCase c v) = uses (c,v)

instance Uses ClockExpr where
  uses (WhenClock _ cv i) = uses cv `mappend` aVal (Unqual i)


instance Uses NodeDecl where
  uses x = uses (nodeStaticInputs x) <>
           ((uses (nodeProfile x) <>
              (uses (nodeContract x, nodeDef x)
                                `without` defines (nodeProfile x)))
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
      Assert _ e -> uses e
      Property _ e -> uses e
      Define lhs e -> uses (lhs,e)
      IsMain _ -> mempty
      IVC is -> Set.fromList [ (ValNS,Unqual i) | i <- is ]

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


instance Uses Contract where
  uses = usesContract . contractItems

instance Uses ContractItem where
  uses ci =
    case ci of
      GhostConst _ mbT e -> uses (mbT, e)
      GhostVar   b     e -> uses (b,e)
      Assume e           -> uses e
      Guarantee e        -> uses e
      Mode _ mas mgs     -> uses (mas,mgs)
      Import x as bs     -> Set.insert (ContractNS,Unqual x) (uses (as,bs))

instance Uses ContractDecl where
  uses = usesContract . cdItems

instance Defines ContractDecl where
  defines c = aContract (Unqual (cdName c))



definesItem :: (?contractInfo :: ContractInfo) => ContractItem -> Names
definesItem ci =
  case ci of
    GhostConst x _ _   -> aVal (Unqual x)
    GhostVar   b _     -> defines b
    Assume _           -> mempty
    Guarantee _        -> mempty
    Mode _ _ _         -> mempty  -- XXX: node references?
    Import x _ _ ->
      case Map.lookup (Unqual x) ?contractInfo of
        Just c  -> c
        Nothing -> panic "definesItem"
                     [ "Unknwon contract in import"
                     , "*** Name: " ++ showPP x
                     ]

definesContract :: (?contractInfo :: ContractInfo) => ContractDecl -> Names
definesContract cd = Set.unions $ aContract (Unqual (cdName cd))
                                : map definesItem (cdItems cd)


usesContract :: (?contractInfo :: ContractInfo) => [ContractItem] -> Names
usesContract cs = uses cs `without` defs
  where
  defs = Set.unions (map definesItem cs)


