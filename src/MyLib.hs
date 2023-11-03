{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module MyLib
where

import Control.Applicative ((<|>))
import Control.Arrow       (second)
import Control.Monad       (when)

import Control.Monad.State
  ( StateT(..)
  , evalStateT
  , get
  , gets
  , put
  )


import Data.Map (Map)
import qualified Data.Map as M

import SoP
import Unify
import Range
import NewtonsMethod
import Data.Maybe (isNothing)


parts :: [a] -> [[a]]
parts [] = []
parts (x:xs) = xs : map (x:) (parts xs)


data Ord c => State c
  = State (Map c (Range c)) [Unifier c]
  deriving (Show)

instance Ord c => Semigroup (State c) where
  (State r1 u1) <> (State r2 u2) = State (M.union r1 r2) (u1 ++ u2)

instance Ord c => Monoid (State c) where
  mempty = State M.empty []

type SolverState c = StateT (State c) Maybe


maybeFail :: (MonadFail m) => Maybe a -> m a
maybeFail (Just a) = return a
maybeFail Nothing = fail ""

getRanges :: (Ord c) => SolverState c (Map c (Range c))
getRanges = gets (\(State rangeS _) -> rangeS)

getRange :: (Ord c) => c -> SolverState c (Range c)
getRange c = maybeFail . M.lookup c =<< getRanges

getRangeSymbol :: (Ord c) => Symbol c -> SolverState c (Range c)
getRangeSymbol (E b p) = maybeFail =<< rangeExp <$> getRangeSoP b <*> getRangeProduct p
getRangeSymbol i@(I _) = return range
  where bound = Bound (toSoP i)
        range = Range bound bound
getRangeSymbol (C c)   = getRange c

getRangeProduct :: (Ord c) => Product c -> SolverState c (Range c)
getRangeProduct p = maybeFail . foldl rm oneRange =<< mapM getRangeSymbol (unP p)
  where
    one = Bound $ toSoP (I 1)
    oneRange = Just (Range one one)
    rm Nothing  _ = Nothing
    rm (Just a) b = rangeMul a b

getRangeSoP :: (Ord c) => SoP c -> SolverState c (Range c)
getRangeSoP s = maybeFail . foldl ra zeroRange =<< mapM getRangeProduct (unS s)
  where
    zero = Bound $ toSoP (I 0)
    zeroRange = Just (Range zero zero)
    ra Nothing _  = Nothing
    ra (Just a) b = rangeAdd a b

putRange :: (Ord c) => c -> Range c -> SolverState c ()
putRange symb range@Range{..} = do
  -- Anti-symmetry: 5 <= x ^ x <= 5 => x = 5
  case (lower == upper, upper) of
    (True,Bound bound) -> putUnifiers [Subst symb (toSoP bound)]
    _                  -> return ()
  (State rangeS unifyS) <- get
  let rangeSn = M.insert symb range rangeS
  put (State rangeSn unifyS)


getUnifiers :: (Ord c) => SolverState c [Unifier c]
getUnifiers = gets (\(State _ unifyS) -> unifyS)

putUnifiers :: (Ord c) => [Unifier c] -> SolverState c ()
putUnifiers us = do
  (State rangeS unifyS) <- get
  put (State rangeS (substsSubst us (us ++ unifyS)))


declareSymbol :: (Ord c) => Symbol c -> SolverState c ()
declareSymbol (I _) = return ()
declareSymbol (C c) = do
  ranges <- getRanges
  when (isNothing (M.lookup c ranges)) (putRange c range)
  where
    range = Range (Bound (toSoP (I 0))) Inf
declareSymbol (E b p) = declareSoP b >> declareProduct p

declareProduct :: (Ord c) => Product c -> SolverState c ()
declareProduct = mapM_ declareSymbol . unP

declareSoP :: (Ord c) => SoP c -> SolverState c ()
declareSoP = mapM_ declareProduct . unS


declareEq :: (Ord c) => SoP c -> SoP c -> SolverState c ()
declareEq (S [P [C x]]) v = declareEq' x v
declareEq u (S [P [C x]]) = declareEq' x u
declareEq u v = putUnifiers $ unifiers u v

declareEq' :: (Ord c) => c -> SoP c -> SolverState c ()
declareEq' x v = putUnifiers [Subst x v]


propagateInEqSymbol :: (Ord c) => Symbol c -> OrdRel -> SoP c -> SolverState c Bool
propagateInEqSymbol (I _) _ _ = return True
propagateInEqSymbol (C c) rel bound = do
  (Range low up) <- getRange c
  case rel of    
    LeR -- Check for update being valid (newUpBound >= lowBound)
      | up == Inf
        -> putRange c (Range low rangeBound)
      | otherwise -- Check for the range not being widened
        -> putRange c (Range low rangeBound)
    GeR -- Check for update being valid (newLowBound <= upBound)
      | low == Bound (toSoP (I 0))
        -> putRange c (Range rangeBound up) 
      | otherwise -- Check for the range not being widened
        -> putRange c (Range rangeBound up)
    EqR -> error "propagateInEqSymbol:EqR: unreachable"
  return True
  where
    rangeBound = Bound bound
-- propagateInEqSymbol (E b (P [I i])) rel target_bound =
--   undefined
-- propagateInEqSymbol (E (S [P [I i]]) p) rel target_bound =
--   undefined
propagateInEqSymbol _ _ _ = fail ""

propagateInEqProduct :: (Ord c) => Product c -> OrdRel -> SoP c -> SolverState c Bool
propagateInEqProduct (P [symb]) rel target_bound = propagateInEqSymbol symb rel target_bound
propagateInEqProduct (P ss) rel target_bound =
  and <$> mapM (uncurry propagate)
    (zipWith (curry (second P)) ss (parts ss))
  where
    propagate symb prod =
      (boundSoP . bound <$> getRangeProduct prod)
      >>= \case Nothing -> fail ""
                (Just current_bound) -> propagateInEqSymbol
                  symb rel
                  target_bound

    bound
      | rel == LeR = \(Range low _) -> low
      | rel == GeR = \(Range _ up)  -> up

propagateInEqSoP :: (Ord c) => SoP c -> OrdRel -> SoP c -> SolverState c Bool
propagateInEqSoP (S [P [symb]]) rel target_bound = propagateInEqSymbol symb rel target_bound
propagateInEqSoP (S ps) rel target_bound =
  and <$> mapM (uncurry propagate) (zipWith (curry (second S)) ps (parts ps))
  where
    propagate prod sm = propagateInEqProduct
                        prod rel
                        (mergeSoPSub target_bound sm)

type Update c = Range c -> SoP c -> SolverState c (Range c)

declareInEq :: (Ord c) => OrdRel -> SoP c -> SoP c -> SolverState c Bool
declareInEq EqR u v = declareEq u v >> return True
declareInEq op u v =
  let
    (u', v') = splitSoP u v
  in do
    -- res <- assert (SoPE u' v' op)
    -- if res then return True
      -- else
    case op of
       LeR -> do
         a1 <- propagateInEqSoP u' LeR v'
         a2 <- propagateInEqSoP v' GeR u'
         return (a1 && a2)
       GeR -> do
         a1 <- propagateInEqSoP u' GeR v'
         a2 <- propagateInEqSoP v' LeR u'
         return (a1 && a2)


declare :: Ord c => SoPE c -> SolverState c Bool
declare SoPE{..} = do
  declareSoP lhs
  declareSoP rhs
  case op of
    EqR -> declareEq lhs rhs >> return True
    _   -> declareInEq op lhs rhs


assertEq :: Ord c => SoP c -> SoP c -> SolverState c Bool
assertEq lhs rhs = do
  us <- getUnifiers
  let
    lhs' = substsSoP us lhs
    rhs' = substsSoP us rhs
  return ((lhs == rhs) || (lhs' == rhs'))

assertRange :: Ord c => SoP c -> SoP c -> SolverState c Bool
assertRange lhs rhs = do
  (Range _ up1) <- getRangeSoP lhs
  (Range low2 _) <- getRangeSoP rhs
  case (up1,low2) of
    (Inf,_) -> return False
    (_,Inf) -> return False
    (Bound (S [P [I i1]]), Bound (S [P [I i2]]))
      -> return (i1 <= i2)
    (Bound ub1,            Bound lb2)
      -> assert (SoPE lhs lb2 LeR)
         <|> assert (SoPE ub1 rhs LeR)
         <|> assert (SoPE ub1 lb2 LeR)

assertNewton :: Ord c => SoP c -> SoP c -> SolverState c Bool
assertNewton lhs rhs = do
  us <- getUnifiers
  let
    lhs' = substsSoP us lhs
    rhs' = substsSoP us rhs
  case (newtonMethod (mergeSoPSub rhs lhs), newtonMethod (mergeSoPSub rhs' lhs')) of
    (Right _, _) -> return False
    (_,Right _) -> return False
    (_,_)       -> return True

assert :: Ord c => SoPE c -> SolverState c Bool
assert SoPE{..} = do
  declareSoP lhs
  declareSoP rhs
  case op of
    EqR -> assertEq lhs rhs
    LeR -> do
      r1 <- assertEq lhs rhs
      if r1 then return True
        else do
        r2 <- assertNewton lhs rhs
        if r2 then return True
          else assertRange lhs rhs
    GeR -> do
      r1 <- assertEq lhs rhs
      if r1 then return True
        else do
        r2 <- assertNewton rhs lhs
        if r2 then return True
          else assertRange rhs lhs

runStatements :: (Ord c) => SolverState c a -> Maybe (a,State c)
runStatements stmts = runStateT stmts mempty

evalStatements :: (Ord c) => SolverState c a -> Maybe a
evalStatements stmts = evalStateT stmts mempty
