{-# Language OverloadedStrings #-}
module Language.Lustre.TypeCheck.Utils where

import Text.PrettyPrint
import Control.Monad(unless)

import Language.Lustre.AST
import Language.Lustre.Pretty
import Language.Lustre.TypeCheck.Monad
import Language.Lustre.TypeCheck.Constraint


-- | Assert that a given expression has only one type (i.e., is not a tuple)
one :: [a] -> M a
one xs =
  case xs of
    [x] -> pure x
    _   -> arityMismatch (length xs) 1

sameLen :: [a] -> [b] -> M ()
sameLen xs ys
  | a == b    = pure ()
  | otherwise = arityMismatch a b
  where
  a = length xs
  b = length ys

arityMismatch :: Int -> Int -> M a
arityMismatch x y =
  reportError $
  nestedError "Arity mismatch."
    [ "Expected arity:" <+> int x
    , "Actual arity:"   <+> int y
    ]

tLUB :: Type -> Type -> M Type
tLUB = undefined

ctLUB :: CType -> CType -> M CType
ctLUB ct1 ct2 =
  do sameClock (cClock ct1) (cClock ct2)
     ty <- tLUB (cType ct1 )(cType ct2)
     pure CType { cClock = cClock ct1, cType = ty }



--------------------------------------------------------------------------------
-- Clocks


-- | Are these the same clock.  If so, return the one that is NOT a 'ConstExpr'
-- (if any).
sameClock :: IClock -> IClock -> M ()
sameClock x0 y0 =
  do x <- zonkClock x0
     y <- zonkClock y0
     case (x,y) of
       (ClockVar a, _) -> bindClockVar a y
       (_, ClockVar a) -> bindClockVar a x
       (BaseClock,BaseClock) -> pure ()
       (KnownClock a, KnownClock b) -> sameKnownClock a b
       _ -> reportError $ nestedError
             "The given clocks are different:"
             [ "Clock 1:" <+> pp x
             , "Clock 2:" <+> pp y
             ]

-- | Is this the same known clock.
sameKnownClock :: ClockExpr -> ClockExpr -> M ()
sameKnownClock c1@(WhenClock _ e1_init i1) c2@(WhenClock _ e2_init i2) =
  do unless (i1 == i2) $
        reportError $
        nestedError
          "The given clocks are different:"
          [ "Clock 1:" <+> pp c1
          , "Clock 2:" <+> pp c2
          ]
     sameConsts e1_init e2_init

-- | Get the clock of a clock, or fail if we are the base clock.
clockParent :: IClock -> M IClock
clockParent ct0 =
  do ct <- zonkClock ct0
     case ct of
       BaseClock -> reportError "The base clock has no parent."
       KnownClock (WhenClock _ _ i) -> cClock <$> lookupLocal i
                                          -- XXX: This can be a constnat?
       ClockVar _ -> reportError "Failed to infer the expressions's clock"



--------------------------------------------------------------------------------
-- Expressions

binConst :: (Integer -> Integer -> Integer) ->
            Expression -> Expression -> M Expression
binConst f e1 e2 =
  do x <- intConst e1
     y <- intConst e2
     pure $ Lit $ Int $ f x y

addExprs :: Expression -> Expression -> M Expression
addExprs = binConst (+) -- XXX: Can make an expression instead

minExprs :: Expression -> Expression -> M Expression
minExprs = binConst min

maxConsts :: Expression -> Expression -> M Expression
maxConsts = binConst max








