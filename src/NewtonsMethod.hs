module NewtonsMethod
  ( newtonMethod
  , evalSoP
  )
where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import SoP
  ( SoP(..)
  , Product(..)
  , Symbol(..)
  , constants)

evalSoP :: (Ord c, Floating n) => SoP c -> Map c n -> n
evalSoP (S []) _ = 0
evalSoP (S ps) binds = sum $ map (`evalProduct` binds) ps

evalProduct :: (Ord c, Floating n) => Product c -> Map c n -> n
evalProduct (P ss) binds = product $ map (`evalSymbol` binds) ss

evalSymbol :: (Ord c, Floating n) => Symbol c -> Map c n -> n
evalSymbol (I i) _     = fromInteger i
evalSymbol (C c) binds = f $ M.lookup c binds
  where f (Just n) = n
        f Nothing  = 0
evalSymbol (E b p) binds = exp (evalProduct p binds * log (evalSoP b binds))

derivative :: (Ord c, Floating n) => SoP c -> c -> (Map c n -> n)
derivative sop symb = \binds -> sum $ d <*> [binds]
  where d = map (`derivativeProduct` symb) $ unS sop

derivativeProduct :: (Ord c, Floating n) => Product c -> c -> (Map c n -> n)
derivativeProduct (P [])     _ = const 0
derivativeProduct (P (s:ss)) symb = \binds -> derivativeSymbol s symb binds * evalProduct ps binds + evalSymbol s binds * derivativeProduct ps symb binds
  where ps = P ss

derivativeSymbol :: (Ord c, Floating n) => Symbol c -> c -> (Map c n -> n)
derivativeSymbol (I _) _ = const 0
derivativeSymbol (C c) symb
  | c == symb = const 1
  | otherwise = const 0
derivativeSymbol e@(E b p) symb = \binds ->
    expExpr binds *
    (derivative b symb binds * evalProduct p binds
      / evalSoP b binds
      + logExpr binds
      * derivativeProduct p symb binds)
  where expExpr = evalSymbol e
        logExpr = log. evalSoP b

newtonMethod :: (Ord c, Ord n, Floating n) => SoP c -> Either (Map c n) (Map c n)
newtonMethod sop = go init_guess 100
  where
    consts     = constants sop
    derivs     = M.fromSet (derivative sop) consts
    init_guess = M.fromSet (const 10) consts

    go guess 0 = Left guess
    go guess n
      | val <= 0.1 = Right guess
      | otherwise =
        let
          new_guess = foldl (\binds (c,x) -> M.insert c (x - val / dsdc c) binds) guess $ M.toList guess
        in go new_guess (n - 1)
      where
        val = evalSoP sop guess
        dsdc c = fromJust (M.lookup c derivs) guess
