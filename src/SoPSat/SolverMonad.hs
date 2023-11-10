{-# LANGUAGE RecordWildCards #-}

module SoPSat.SolverMonad
  ( -- * State
    SolverState
  , State
  -- * Getters/setters
  , getRanges
  , getRange
  , getRangeSoP
  , putRange
  , getUnifiers
  , putUnifiers
  -- * Execution
  , runStatements
  , evalStatements
  )
where

import Control.Monad.State
  ( StateT(..)
  , evalStateT
  , get
  , gets
  , put
  )


import Data.Map (Map)
import qualified Data.Map as M

import SoPSat.SoP
import SoPSat.Unify
import SoPSat.Range


data Ord c => State c
  = State (Map c (Range c)) [Unifier c]
  deriving (Show)

instance Ord c => Semigroup (State c) where
  (State r1 u1) <> (State r2 u2) = State (M.union r1 r2) (u1 ++ u2)

instance Ord c => Monoid (State c) where
  mempty = State M.empty []

-- TODO: Change Maybe to some MonadError for better error indication
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
  put (State rangeS (substsSubst us unifyS ++ us))


-- ^ Runs computation returning result and resulting state
runStatements :: (Ord c) => SolverState c a -> Maybe (a,State c)
runStatements stmts = runStateT stmts mempty

-- ^ Similar to @runStatements@ but does not return final state
evalStatements :: (Ord c) => SolverState c a -> Maybe a
evalStatements stmts = evalStateT stmts mempty
