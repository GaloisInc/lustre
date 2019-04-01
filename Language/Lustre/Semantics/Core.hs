{-# Language MultiWayIf, OverloadedStrings #-}
module Language.Lustre.Semantics.Core where

import Data.List(foldl')
import Data.Maybe(fromMaybe)
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Text.PrettyPrint

import Language.Lustre.Panic
import Language.Lustre.Pretty
import Language.Lustre.Name(Ident)
import Language.Lustre.Core
import Language.Lustre.Semantics.BuiltIn(eucledean_div_mod)

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

instance Pretty Value where
  ppPrec _ = ppValue


data State = State
  { sValues :: Map Ident Value
    -- ^ Values for identifiers.
    -- If a value is missing, then its value is assumed to be 'VNil'.

  , sInitialized :: Set Ident
    -- ^ Additional state to implement @a -> b@
    -- Contains the identifiers that have transition to the second phase.
  }

ppState :: PPInfo -> State -> Doc
ppState info s =
    vcat [ "values:"
         , nest 2 (vcat (map ppV (Map.toList (sValues s))))
         , "initialized:" <+> commaSep (map ppI (Set.toList (sInitialized s)))
         ]
    where
    ppI = ppIdent info
    ppV (x,y) = ppI x <+> "=" <+> pp y



instance Pretty State where
  ppPrec _ = ppState noInfo

initNode :: Node ->
            Maybe (Map Ident Value) {- Optional inital values -} ->
            (State, State -> Map Ident Value -> State)
initNode node mbStart = (s0, stepNode node1 env)
  where
  s0     = State { sInitialized = Set.empty
                 , sValues = fromMaybe Map.empty mbStart
                 }
  env    = nodeEnv node
  node1  = case orderedEqns (nEqns node) of
             Right ok -> node { nEqns = ok }
             Left err -> panic "initNode" [ "Failed to order equations"
                                          , "*** Recursive: " ++ show err ]


stepNode :: Node              {- ^ Node, with equations properly ordered -} ->
            (Map Ident CType) {- ^ Types of identifiers -} ->
            State             {- ^ Current state -} ->
            Map Ident Value   {- ^ Inputs -} ->
            State             {- ^ Next state -}
stepNode node env old ins = foldl' (evalEqn env old) new (nEqns node)
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


evalEqn :: Map Ident CType {- ^ Types of identifier    -} ->
           State           {- ^ Old state              -} ->
           State           {- ^ New state (partial)    -} ->
           Eqn             {- ^ Equation to evaluate   -} ->
           State           {- ^ Updated new state      -}

evalEqn env old new (x ::: _ `On` c := expr) =
  case expr of

    Atom a    -> guarded $ done $ evalAtom new a
    Current a -> done (evalAtom new a)

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

  guarded = guardedOn c

  guardedOn cl v =
    case cl of
      Lit b -> case b of
                 Bool True  -> v    -- base clock
                 Bool False -> hold -- weird always false clock
                 _ -> panic "guardedOn" [ "Non boolean clock" ]
      _ -> case evalAtom new cl of
             VBool True -> guardedOn (clockOfCType (typeOf env cl)) v
             _ -> hold
    where hold = new { sValues = Map.insert x (evalVar old x) (sValues new) }





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

     FloorCast ->
       case vs of
         [ VNil ]     -> VNil
         [ VReal r ]  -> VInt (floor r)
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
         [ VInt x, VInt y ]    -> case eucledean_div_mod x y of
                                    Just (q,_) -> VInt q
                                    Nothing    -> VNil -- ?
         [ VReal x, VReal y ]  -> VReal (x / y)
         _                     -> bad "2 numbers"

     Mod ->
       case vs of
         [ VNil, _ ]           -> VNil
         [ _, VNil ]           -> VNil
         [ VInt x, VInt y ]    -> case eucledean_div_mod x y of
                                    Just (_,r) -> VInt r
                                    Nothing    -> VNil -- ?
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






