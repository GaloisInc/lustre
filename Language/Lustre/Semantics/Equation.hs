{-# Language RecursiveDo #-}
module Language.Lustre.Semantics.Equation where

import Control.Monad(liftM2)
import Data.Either(partitionEithers)
import Data.Map(Map)
import Data.List(groupBy)
import qualified Data.Map as Map

import Language.Lustre.AST
import Language.Lustre.Semantics.Value
import Language.Lustre.Semantics.Env
import Language.Lustre.Semantics.Expression


-- | Evaluate a bunch of mutually recursive equations.
-- The result are the defines values, and the values of assertions.
evalEquations ::
  Env -> [ Equation ] -> EvalM (Map Ident ReactValue, [ReactValue])
evalEquations env es =
  do lhs     <- mapM (mapM (evalLHS env)) ldefs
     rec vss <- mapM (evalMultiExpr newEnv) rdefs
         let newDefs = makeEnvDelta lhs vss
             newEnv  = env { envLocals = Map.union newDefs (envLocals env) }
     avs <- mapM (evalExpr newEnv) asts
     pure (newDefs, avs)
  where
  (asts,defs)   = partitionEithers (map classify es)
  (ldefs,rdefs) = unzip defs

  classify eqn = case eqn of
                   Assert e -> Left e
                   Define bs e -> Right (bs,e)


evalLHS :: Env -> LHS Expression -> EvalM (LHS Value)
evalLHS env lhs =
  case lhs of
    LVar x -> pure (LVar x)
    LSelect l s ->
      do l1 <- evalLHS env l
         s1 <- evalSel env s
         pure (LSelect l1 s1)

-- | No error checking; assumes declarations have been checked.
makeEnvDelta :: [ [LHS Value] ] -> [ [ReactValue] ] -> Map Ident ReactValue
makeEnvDelta lhs vss = buildValues $ Map.unions $ zipWithL makeDefs lhs vss

-- | It is important here that we are completely lazy in the incoming
-- reactive values.
buildValues :: Map LHSName ReactValue -> Map Ident ReactValue
buildValues mp
  | Map.null todoMap = doneMap
  | otherwise        = Map.union doneMap (buildValues todoMap)
  where
  (todoList,doneList) =
     partitionEithers $ map makeLayer $ groupBy partOfSameVal $ Map.toList mp

  doneMap = Map.fromList doneList
  todoMap = Map.fromList todoList


  makeLayer ds =
    case fst (head ds) of
      ArrayElement x _ ->
        Left (x, mkArray undefined (map snd ds))
      StructField x _  ->
        Left (x, mkStruct undefined undefined [ (f,v) | (StructField _ f, v) <- ds ])
      Root x -> Right (x, snd (head ds))

  partOfSameVal (x,_) (y,_) = sameVal x y

  sameVal a b =
    case (a,b) of
      (Root x, Root y) -> x == y
      (ArrayElement u _, ArrayElement v _) -> sameVal u v
      (StructField u _, StructField v _) -> sameVal u v
      _ -> False

-- | Force the value to emit as specified by the given clock.
usingClock :: ReactValue {-^ Value -} -> ReactValue {-^ clock -} -> ReactValue
usingClock ~(Stream v vs) (Stream c cs) = Stream step rest
  where
  step = case c of
           Skip n -> Skip n
           Emit _ -> v

  rest = liftM2 usingClock vs cs



mkArray :: ReactValue -> [ ReactValue ] -> ReactValue
mkArray (Stream c cs) vs = Stream now next
  where
  now = case c of
          Emit (VBool True)  -> Emit (VArray (map hd vs))
          Emit (VBool False) -> Skip 0
          Emit _             -> error "mkArray" "clock error"
          Skip n             -> Skip n

  next = do c1  <- cs
            vs1 <- mapM tl vs
            pure (mkArray c1 vs1)

  hd (Stream ~(Emit v) _) = v
  tl (Stream _ n) = n

mkStruct :: Name -> ReactValue -> [ (Ident,ReactValue) ] -> ReactValue
mkStruct t (Stream c cs) vs = Stream now next
  where
  now = case c of
          Emit (VBool True)  -> Emit (VStruct t (map hd vs))
          Emit (VBool False) -> Skip 0
          Emit _             -> error "mkStruct " "clock error"
          Skip n             -> Skip n

  next = do c1  <- cs
            vs1 <- mapM tl vs
            pure (mkStruct t c1 vs1)

  hd (f, Stream ~(Emit v) _) = (f, v)
  tl (f, Stream _ n) = do s <- n
                          pure (f, s)




makeDef :: LHS Value -> ReactValue -> Map LHSName ReactValue
makeDef = undefined



data LHSName = Root Ident
             | ArrayElement LHSName Integer
             | StructField LHSName Ident
               deriving (Show,Eq,Ord)

makeDefs :: [LHS Value] -> [ReactValue] -> Map LHSName ReactValue
makeDefs ls vs = Map.unions (zipWithL makeDef ls vs)

zipWithL :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWithL f (x : xs) ~(y : ys) = f x y : zipWithL f xs ys
zipWithL _ []       _         = []











