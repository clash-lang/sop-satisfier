{-# LANGUAGE ScopedTypeVariables #-}

module SoPSat.Internal.NewtonsMethod
where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import SoPSat.Internal.SoP (
  Atom (..),
  Product (..),
  SoP (..),
  Symbol (..),
 )
import SoPSat.SoP (atoms)

-- | Evaluates SoP given atom bindings
evalSoP ::
  (Ord f, Ord c, Floating n) =>
  -- | Expression to evaluate
  SoP f c ->
  -- | Bindings from atoms to values
  Map (Atom f c) n ->
  -- | Evaluation result
  n
evalSoP (S []) _ = 0
evalSoP (S ps) binds = sum $ map (`evalProduct` binds) ps

{- | Evaluates product given atom bindings

Used by @evalSoP@
-}
evalProduct ::
  (Ord f, Ord c, Floating n) =>
  -- | Product to evalute
  Product f c ->
  -- | Atom bindings
  Map (Atom f c) n ->
  -- | Evaluation results
  n
evalProduct (P ss) binds = product $ map (`evalSymbol` binds) ss

{- | Evaluates symbol given atom bindings

Used by @evalProduct@
-}
evalSymbol ::
  (Ord f, Ord c, Floating n) =>
  -- | Symbol to evaluate
  Symbol f c ->
  -- | Atom bindings
  Map (Atom f c) n ->
  -- | Evaluation result
  n
evalSymbol (I i) _ = fromInteger i
evalSymbol (A a) binds = f $ M.lookup a binds
 where
  f (Just n) = n
  f Nothing = 0
evalSymbol (E b p) binds = exp (evalProduct p binds * log (evalSoP b binds))

{- | Analitically computes derivative of an expression
with respect to an atom

Returns function similar to @evalSoP@
-}
derivative ::
  (Ord f, Ord c, Floating n) =>
  -- | Expression to take a derivative of
  SoP f c ->
  -- | Atom to take a derivetive with respect to
  Atom f c ->
  -- | Function from bindings, representing point,
  -- to value of the derivative at that point
  (Map (Atom f c) n -> n)
derivative sop symb = \binds -> sum $ d <*> [binds]
 where
  d = map (`derivativeProduct` symb) $ unS sop

{- | Analitically computes derivative of a product
with respect to an atom

Used by @derivative@
-}
derivativeProduct ::
  (Ord f, Ord c, Floating n) =>
  -- | Product to take a derivative of
  Product f c ->
  -- | Atom to take a derivative with respect to
  Atom f c ->
  -- | Function from bindings to a value
  (Map (Atom f c) n -> n)
derivativeProduct (P []) _ = const 0
derivativeProduct (P (s : ss)) symb = \binds ->
  derivativeSymbol s symb binds * evalProduct ps binds
    + evalSymbol s binds * derivativeProduct ps symb binds
 where
  ps = P ss

{- | Analitically computes derivative of a symbol
with respect to an atom

Used by @derivativeProduct@
-}
derivativeSymbol ::
  (Ord f, Ord c, Floating n) =>
  -- | Symbol to take a derivate of
  Symbol f c ->
  -- | Atom to take a derivate with respect to
  Atom f c ->
  -- | Function from bindings to a value
  (Map (Atom f c) n -> n)
derivativeSymbol (I _) _ = const 0
derivativeSymbol (A a) atom
  | a == atom = const 1
  | otherwise = const 0
derivativeSymbol e@(E b p) atom = \binds ->
  expExpr binds
    * ( derivative b atom binds
          * evalProduct p binds
          / evalSoP b binds
          + logExpr binds
            * derivativeProduct p atom binds
      )
 where
  expExpr = evalSymbol e
  logExpr = log . evalSoP b

-- | Finds if an expression can be equal to zero
newtonMethod ::
  forall f c n.
  (Ord f, Ord c, Ord n, Floating n) =>
  -- | Expression to check
  SoP f c ->
  -- | @Right binds@ - Atom bindings when expression is equal to zero
  --   @Left binds@ - Last checked bindings
  Either (Map (Atom f c) n) (Map (Atom f c) n)
newtonMethod sop = go init_guess steps
 where
  consts = atoms sop
  derivs = M.fromSet (derivative sop) consts
  init_guess = M.fromSet (const 10) consts
  steps = 40

  go :: Map (Atom f c) n -> Word -> Either (Map (Atom f c) n) (Map (Atom f c) n)
  go guess 0 = Left guess
  go guess n
    | val <= 0.1 = Right guess
    | otherwise =
        let
          new_guess = foldl (\binds (c, x) -> M.insert c (x - val / dsdc c) binds) guess $ M.toList guess
         in
          go new_guess (n - 1)
   where
    val = evalSoP sop guess
    dsdc c = fromJust (M.lookup c derivs) guess
