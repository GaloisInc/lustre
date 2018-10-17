module Language.Lustre.TypeCheck where

import Data.Map(Map)
import qualified Data.Map as Map

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.Panic

-- | A clock variable stays for a fixed but unknown clock.
-- Used to handle constants, which can have whatever clock we want.
data TVar       = TVar { tvarId     :: !Int
                       , tvarSource :: SourceRange
                       }

instance Eq TVar where
  x == y = tvarId x == tvarId y

instance Ord TVar where
  compare x y = compare (tvarId x) (tvarId y)


-- | A single clock expression.
data IClock     = ClockVar TVar
                | BaseClock
                | KnownClock ClockExpr
                | NestedClock IClock IClock  -- ^ current, clock of clock

data IType      = IInt | IBool | IReal
                | IEnum Name
                | IStruct Name
                | IArray Expression IType
                | ITuple [IType] -- XXX: Perhaps tuples should be a CType?
                | IVar TVar

-- | A type, together with its clock.
data CType      = CType { cType :: IType, cClock :: IClock }


checkConstExpr :: Expression -> M IType
checkConstExpr expr =
  case expr of
    ERange r e -> inRange r (checkConstExpr r e)
    Var x      -> checkConst x
    Lit l      -> pure (checkLit l)
    _ `When` _ -> reportError "`when` is not a constant expression."
    Tuple {}   -> reportError "tuples cannot be used in constant expressions."
    Array es   ->
      do ts <- mapM checkConstExpr es
         t  <- case ts of
                 []     -> freshType
                 a : bs -> do mapM_ (sameType a) bs
                              pure a
         let n = Lit $ Int $ fromIntgral $ length es
         pure (IArray n t)

    Struct {} -> undefined
    Select {} -> undefined

    WithThenElse e1 e2 e3 ->
      do t <- checkConstExpr e1
         sameType t IBool
         x <- checkConstExpr e2
         y <- checkConstExpr e3
         sameType x y
         pure x

    Merge {} -> reportError "`merge` is not a constant expression."

    CallPos {} -> reportError "constant expressions do not support calls."


checkExpr :: Expression -> M CType
checkExpr expr =
  case expr of
    ERange r e -> inRange r (checkExpr e)

    Var x      -> checkVar x

    Lit l ->
      do let t = checkLit l
         c <- freshClock
         pure CType { cType = t, cClock = c }

    e `When` c            ->
      do t1 <- checkExpr e
         c1 <- checkClockExpr c
         sameClock (cClock t1) c1
         pure CType { cType  = cType t1
                    , cClock = NestedClock (KnownClock c) c1 }

    Tuple es ->
      do ts <- mapM checkExpr es
         c  <- case map cClock ts of
                c : more -> do mapM_ (sameClock c) more
                               pure c
                [] -> freshClock
         pure CType { cType = ITuple (map cType ts), cClock = c }

    Array es ->
      do ts <- mapM checkExpr es
         t  <- case ts of
                 t : more -> do mapM_ (sameCType t) more
                                pure t
                 []       -> freshCType
         let n = Lit $ Int $ fromIntegral $ length es
         pure t { cType = IArray n (cType t) }



    Select {} -> undefined
    Struct {} -> undefined

    WithThenElse e1 e2 e3 ->
      do t1 <- checkConstExpr e1
         sameType IBool t1
         a  <- checkExpr e2
         b  <- checkExpr e3
         sameCType a b
         pure b

    Merge i as ->
      do t   <- lookupIdent i
         ats <- mapM (checkMergeCase i t) as
         r   <- case ats of
                  [] -> reportError "Empty `merge`"
                  r : more ->
                    do mapM_ (sameType r) more
                       pure r
         -- XXX: Check all cases matched
         pure CType { cType = r, cClock = cClock t }


    CallPos (NodeInst call as) es ->
      case as of
        []
          | CallPrim r (Op2 Replicate) <- call ->
            inRange r $
            case es of
              [e1,e2] ->
                do t1 <- checkExpr e1
                   t2 <- checkConstExpr e2
                   sameType t2 IInt
                   pure t1 { cType = IArray e2 (cType t1) }
              _ -> reportError (showPP call ++ " expexts 2 arguments.")

          | otherwise ->
          do ts <- mapM checkExpr es
             case call of
               CallUser f -> undefined
               CallPrim r prim -> inRange r $
                 case prim of

                   Op1 op1 ->
                     case ts of
                       [t] -> checkOp1 op1 t
                       _   -> reportError (showPP op1 ++ " expects 1 argument.")

                   Op2 op2 ->
                      case ts of
                        [t1,t2] -> checkOp2 op2 t1 t2
                        _ -> reportError (showPP op2 ++ " expects 2 arguments.")

                   ITE ->
                     case ts of
                       [t1,t2,t3] ->
                          do sameType (cType t1) IBool
                             sameClock (cClock t1) (cClock t2)
                             sameCType t2 t3
                             pure t2
                       _ -> reportError "`if-then-else` expects 3 arguments."

                   -- IMPORTANT: For the moment these all work with bools, so we
                   -- just do them in one go.  This may change if we add
                   -- other operators!
                   OpN _ ->
                     do c <- case map cClock ts of
                               [] -> freshClock
                               t : ss -> do mapM_ (sameClock t) ss
                                            pure t
                        mapM_ (sameType IBool . cType) ts
                        pure CType { cType = IBool, cClock = c }

        _ -> undefined


checkMergeCase :: Ident -> CType -> MergeCase -> M IType
checkMergeCase i it (MergeCase p e) =
  do t <- checkConstExpr p
     sameType t (cType it)
     c <- checkExpr e
     let this = KnownClock (WhenClock (range p) p i)
     let expect = NestedClock this (cClock it)
     sameClock expect (cClock it)
     pure (cType c)

checkOp1 :: Op1 -> CType -> M CType
checkOp1 op t =
  case op of
    Pre -> pure t

    Current ->
      do c <- clockParent (cClock t)
         pure t { cClock = c }

    Not ->
      do sameType (cType t) IBool
         pure t

    Neg ->
      do isNumType (cType t)
         pure t

    IntCast ->
      do sameType (cType t) IReal
         pure t { cType = IInt }

    RealCast ->
      do sameType (cType t) IInt
         pure t { cType = IReal }

checkOp2 :: Op2 -> CType -> CType -> M CType
checkOp2 op2 x y =
  do sameClock (cClock x) (cClock y)
     case op2 of
       FbyArr   -> same
       Fby      -> same
       And      -> sameType (cType x) IBool >> same
       Or       -> sameType (cType x) IBool >> same
       Xor      -> sameType (cType x) IBool >> same
       Implies  -> sameType (cType x) IBool >> same
       Eq       -> same >> bool
       Neq      -> same >> bool
       Lt       -> same >> isNum x >> bool
       Leq      -> same >> isNum x >> bool
       Gt       -> same >> isNum x >> bool
       Geq      -> same >> isNum x >> bool
       Add      -> isNum x >> same
       Sub      -> isNum x >> same
       Mul      -> isNum x >> same
       Div      -> isNum x >> same
       Mod      -> isNum x >> same
       Power    -> do isNum x
                      sameType (cType y) IInt
                      pure y
       Replicate -> panic "checkOp2" [ "`replicate` should have been checked."]

       Concat ->
         do sameClock (cClock x) (cClock y)
            x' <- zonkType (cType x)
            y' <- zonkType (cType y)
            case (x',y') of
              (IArray n t1, IArray m t2) ->
                do sameType t1 t2
                   l <- addConsts n m
                   pure CType { cType = IArray l t1, cClock = cClock x }
              _ -> reportError "`|` expects two arrays."
  where
  same = do sameType (cType x) (cType y)
            pure x

  bool = pure CType { cType = IBool, cClock = cClock x }

  isNum a = isNumType (cType a)

addConsts :: Expression -> Expression -> M Expression
addConsts x y =
  case (x,y) of
    (ERange _ x', _)           -> addConsts x' y
    (_, ERange _ y')           -> addConsts x y'
    (Lit (Int a), Lit (Int b)) -> pure (Lit (Int (a + b)))
    _ -> reportError "I don't know how to add the lenghts of the arrays in `|`"

checkVar :: Name -> M CType
checkVar x =
  case x of
    Unqual i -> do mb <- lookupIdentMaybe i
                   case mb of
                     Just c  -> pure c
                     Nothing -> checkConst x
    Qual {}  -> checkConst x

checkConst :: Name -> M CType
checkConst x =
  inRange (range x) $
  do t <- lookupConst x
     c <- freshClock
     pure CType { cType = t, cClock = c }

checkLit :: Literal -> IType
checkLit lit =
     case lit of
       Int _   -> IInt
       Real _  -> IReal
       Bool _  -> IBool

-- | Returns the clock of the clock expression.
checkClockExpr :: ClockExpr -> M IClock
checkClockExpr = undefined

--------------------------------------------------------------------------------

type M = IO

data RO = RO
  { roConstants :: Map Name Type
  , roUserNodes :: Map Name NodeProfile
  , roIdents    :: Map Ident (Type,ClockExpr)
  , roCurRange  :: Maybe SourceRange
  }

data RW = RW
  { rwClockSubst :: !(Map TVar IClock)
  , rwNextVar    :: !Int
  }

sameCType :: CType -> CType -> M ()
sameCType t1 t2 =
  do sameType  (cType t1) (cType t2)
     sameClock (cClock t1) (cClock t2)

sameClock :: IClock -> IClock -> M ()
sameClock x0 y0 =
  do x <- zonkClock x0
     y <- zonkClock y0
     case (x,y) of
       (ClockVar c,_) -> setClockVar c y
       (_,ClockVar c) -> setClockVar c x
       (BaseClock,BaseClock) -> pure ()
       (KnownClock a, KnownClock b)
          | sameKnownClock a b -> pure ()
       (KnownClock {}, NestedClock {}) -> sameClock (NestedClock x BaseClock) y
       (NestedClock {},KnownClock {})  -> sameClock (NestedClock y BaseClock) x
       (NestedClock a b, NestedClock c d) ->
          do sameClock a c
             sameClock b d
       _ -> reportError "Clock mismatch."

sameKnownClock :: ClockExpr -> ClockExpr -> Bool
sameKnownClock (WhenClock _ e1_init i1) (WhenClock _ e2_init i2) =
  i1 == i2 && sameExpr e1_init e2_init
  where
  sameExpr e1 e2 =
    case (e1,e2) of
      (ERange _ e1', _) -> sameExpr e1' e2
      (_, ERange _ e2') -> sameExpr e1 e2'
      (Var x, Var y)    -> x == y  -- expand constants?
      (Lit x, Lit y)    -> x == y
      _                 -> False

setClockVar :: TVar -> IClock -> M ()
setClockVar x ic =
  case ic of
    ClockVar y | x == y -> pure ()
    _ | occurs ic       -> reportError "Clock mistmach (occurs)"
    _                   -> extClockSubst x ic
  where
  occurs c = case c of
               ClockVar y      -> x == y
               KnownClock _    -> False
               BaseClock       -> False
               NestedClock a b -> occurs a || occurs b

-- | Apply the current substitution to the given clock expression.
zonkClock :: IClock -> M IClock
zonkClock c = (`apSubstClock` c) <$> getClockSubst

zonkType :: IType -> M IType
zonkType t = (`apSubstType` t) <$> getTypeSubst

apSubstClock :: Map TVar IClock -> IClock -> IClock
apSubstClock su c =
  case c of
    ClockVar y      -> Map.findWithDefault c y su
    NestedClock a b -> NestedClock (apSubstClock su a) (apSubstClock su b)
    BaseClock       -> c
    KnownClock {}   -> c

apSubstType :: Map TVar IType -> IType -> IType
apSubstType su t =
  case t of
    IVar x      -> Map.findWithDefault t x su
    IInt        -> t
    IBool       -> t
    IReal       -> t
    IEnum {}    -> t
    IStruct {}  -> t
    IArray n s  -> IArray n (apSubstType su s)
    ITuple ts   -> ITuple (map (apSubstType su) ts)

clockParent :: IClock -> M IClock
clockParent ct0 =
  do ct <- zonkClock ct0
     case ct of
       BaseClock    -> reportError "The base clock has not parent."
       KnownClock _ -> pure BaseClock
       ClockVar _   ->
         do c <- freshClock
            p <- freshClock
            sameClock ct (NestedClock c p)
            pure p
       NestedClock _ p -> pure p

sameType :: IType -> IType -> M ()
sameType = undefined

isNumType :: IType -> M ()
isNumType = undefined


-- | Assumes the 'IClock' is zonked.
extClockSubst :: TVar -> IClock -> M ()
extClockSubst = undefined

getClockSubst :: M (Map TVar IClock)
getClockSubst = undefined

getTypeSubst :: M (Map TVar IType)
getTypeSubst = undefined

reportError :: String -> M a
reportError = undefined

inRange :: SourceRange -> M a -> M a
inRange = undefined

freshClock :: M IClock
freshClock = undefined

freshType :: M IType
freshType = undefined

freshCType :: M CType
freshCType =
  do c <- freshClock
     t <- freshType
     pure CType { cType = t, cClock = c }


lookupIdentMaybe :: Ident -> M (Maybe CType)
lookupIdentMaybe = undefined

lookupIdent :: Ident -> M CType
lookupIdent i =
  do mb <- lookupIdentMaybe i
     case mb of
       Just t  -> pure t
       Nothing -> reportError ("Undefined identifier: " ++ showPP i)

lookupConst :: Name -> M IType
lookupConst = undefined

