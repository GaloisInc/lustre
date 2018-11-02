{-# Language MultiWayIf #-}
module Language.Lustre.Semantics.Core where

import Data.List(foldl')
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Text.PrettyPrint(integer,double,text,Doc)

import Language.Lustre.Panic
import Language.Lustre.Core

data Value    = VInt    !Integer
              | VBool   !Bool
              | VReal   !Rational
              | VNil
                deriving Show

isNil :: Value -> Bool
isNil v =
  case v of
    VNil -> True
    _    -> False

isBool :: Value -> Maybe Bool
isBool v =
  case v of
    VBool b -> Just b
    _       -> Nothing

ppValue :: Value -> Doc
ppValue val =
  case val of
    VInt x  -> integer x
    VBool x -> text (show x)
    VReal x -> double (fromRational x)
    VNil    -> text "nil"

data State = State
  { sValues :: Map Ident Value
    -- ^ Values for identifiers.
    -- If a value is missing, then its value is assumed to be 'VNil'.

  , sInitialized :: Set Ident
    -- ^ Additional state to implement @a -> b@
    -- Contains the identifiers that have transition to the second phase.
  }


initNode :: Node -> (State, State -> Map Ident Value -> State)
initNode node = (s0, stepNode node1)
  where
  s0     = State { sInitialized = Set.empty, sValues = Map.empty }
  node1  = case orderedEqns (nEqns node) of
             Right ok -> node { nEqns = ok }
             Left err -> panic "initNode" [ "Failed to order equations"
                                          , "*** Recursive: " ++ show err ]


stepNode :: Node            {- ^ Node, with equations properly ordered -} ->
            State           {- ^ Current state -} ->
            Map Ident Value {- ^ Inputs -} ->
            State           {- ^ Next state -}
stepNode node old ins = foldl' (evalEqn old) new (nEqns node)
  where
  new = State { sInitialized = sInitialized old
              , sValues      = ins
              }


-- | The meaning of a literal.
evalLit :: Literal -> Value
evalLit lit =
  case lit of
    Int i  -> VInt i
    Real r -> VReal r
    Bool b -> VBool b

-- | Lookup the value of a variable.
evalVar :: State -> Ident -> Value
evalVar s x = Map.findWithDefault VNil x (sValues s)

-- | Interpret an atom in the given state.
evalAtom :: State {-^ Environment to for values of variables -} ->
            Atom  {-^ Evaluate this -} ->
            Value {-^ Value of the atom -}
evalAtom s atom =
  case atom of
    Lit l -> evalLit l
    Var x -> evalVar s x
    Prim op as -> evalPrimOp op (map (evalAtom s) as)


evalEqn :: State           {- ^ Old state              -} ->
           State           {- ^ New state (partial)    -} ->
           Eqn             {- ^ Equation to evaluate   -} ->
           State           {- ^ Updated new state      -}

evalEqn old new (x ::: _ `On` c := expr) =
  case expr of

    Atom a      -> done (evalAtom new a)
    Current a   -> done (evalAtom new a)

    a `When` _  ->
      guarded $ done $
      evalAtom new a

    Pre a ->
      guarded $ done $
      evalAtom old a

    a :-> b ->
      guarded $
       if | x `Set.member` sInitialized old -> done (evalAtom new b)
          | VBool True <- evalAtom new c    -> initialized new'
          | otherwise                       -> new'
      where new' = done (evalAtom new a)

    Merge a ifT ifF ->
      guarded $ done $
      case evalAtom new a of
        VBool b -> evalAtom new (if b then ifT else ifF)
        VNil    -> VNil
        _       -> panic "evalEqn" [ "Merge expected a bool" ]


  where
  done v        = new { sValues = Map.insert x v (sValues new) }
  initialized s = s { sInitialized = Set.insert x (sInitialized s) }

  guarded v =
    case evalAtom new c of
     VBool True -> v
     _ ->   new { sValues = Map.insert x (evalVar old x) (sValues new) }



-- | Semantics of primitive operators.
evalPrimOp :: Op -> [Value] -> Value
evalPrimOp op vs =
   case op of
     Not ->
       case vs of
         [ VNil ]    -> VNil
         [ VBool b ] -> VBool (not b)
         _           -> bad "1 bool"

     Neg ->
       case vs of
         [ VNil ]     -> VNil
         [ VInt n ]   -> VInt (negate n)
         [ VReal n ]  -> VReal (negate n)
         _            -> bad "1 number"

     IntCast ->
       case vs of
         [ VNil ]     -> VNil
         [ VReal r ]  -> VInt (truncate r)
         _            -> bad "1 real"

     RealCast ->
       case vs of
         [ VNil ]   -> VNil
         [ VInt n ] -> VReal (fromInteger n)
         _          -> bad "1 int"

     And ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VBool x, VBool y ]  -> VBool (x && y)
         _                     -> bad "2 bools"

     Or ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VBool x, VBool y ]  -> VBool (x || y)
         _                     -> bad "2 bools"

     Xor ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VBool x, VBool y ]  -> VBool (x /= y)
         _                     -> bad "2 bools"

     Implies ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VBool x, VBool y ]  -> VBool (not x || y)
         _                     -> bad "2 bools"

     Eq ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VBool x, VBool y ]  -> VBool (x == y)
         [ VInt x, VInt y ]    -> VBool (x == y)
         [ VReal x, VReal y ]  -> VBool (x == y)
         _                     -> bad "2 of the same type"

     Neq ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VBool x, VBool y ]  -> VBool (x /= y)
         [ VInt x, VInt y ]    -> VBool (x /= y)
         [ VReal x, VReal y ]  -> VBool (x /= y)
         _                     -> bad "2 of the same type"

     Lt ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VBool (x < y)
         [ VReal x, VReal y ]  -> VBool (x < y)
         _                     -> bad "2 numbers"

     Leq ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VBool (x <= y)
         [ VReal x, VReal y ]  -> VBool (x <= y)
         _                     -> bad "2 numbers"

     Gt ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VBool (x > y)
         [ VReal x, VReal y ]  -> VBool (x > y)
         _                     -> bad "2 numbers"

     Geq ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VBool (x >= y)
         [ VReal x, VReal y ]   -> VBool (x >= y)
         _                     -> bad "2 numbers"

     Add ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VInt  (x + y)
         [ VReal x, VReal y ]   -> VReal (x + y)
         _                     -> bad "2 numbers"

     Sub ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VInt  (x - y)
         [ VReal x, VReal y ]   -> VReal (x - y)
         _                     -> bad "2 numbers"

     Mul ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VInt  (x * y)
         [ VReal x, VReal y ]   -> VReal (x * y)
         _                     -> bad "2 numbers"

     Div ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VInt (quot x y)
         [ VReal x, VReal y ]   -> VReal (x / y)
         _                     -> bad "2 numbers"

     Mod ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VInt (rem x y)
         _                     -> bad "2 ints"

     Power ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> VInt  (x ^ y)
         [ VReal x, VInt y ]   -> VReal (x ^ y)
         _                     -> bad "1 number and 1 int"

     ITE ->
       case vs of
         [ VNil, _, _ ]        -> VNil
         [ VBool b, x, y ]     -> if b then x else y -- should we check for Nil?
         _                     -> bad "1 bool, and 2 of the same type"

     AtMostOne
       | any isNil vs              -> VNil
       | Just bs <- mapM isBool vs -> VBool $ case filter id bs of
                                                _ : _ : _ -> False
                                                _         -> True
       | otherwise                 -> bad "all bool"

     Nor
       | any isNil vs              -> VNil
       | Just bs <- mapM isBool vs -> VBool (not (or bs))
       | otherwise                 -> bad "all booleans"

   where
   bad y = panic "evalExpr" [ "Type error:"
                            , "*** Operator: " ++ show op
                            , "*** Expected: " ++ y
                            , "*** Got: "      ++ show vs ]






