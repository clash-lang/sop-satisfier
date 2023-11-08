{-# LANGUAGE RecordWildCards #-}

module SoPSat.Unify
where

import Data.List (intersect, (\\), nub, partition)
import Data.Function (on)

import SoPSat.SoP (SoP (..), Product (..), Symbol (..),
            toSoP, normaliseExp, mergeSoPAdd, mergeSoPMul)


data Unifier c
  = Subst { sConst :: c
          , sSoP   :: SoP c
          }
  | Unify { sLHS   :: SoP c
          , sRHS   :: SoP c
          }
  deriving (Eq, Show)

substsSoP :: (Ord c) => [Unifier c] -> SoP c -> SoP c
substsSoP [] u = u
substsSoP ((Subst{..}):s) u = substsSoP s (substSoP sConst sSoP u)
substsSoP ((Unify{}):s)   u = substsSoP s u

substSoP :: (Ord c) => c -> SoP c -> SoP c -> SoP c
substSoP cons subs = foldr1 mergeSoPAdd . map (substProduct cons subs) . unS

substProduct :: (Ord c) => c -> SoP c -> Product c -> SoP c
substProduct cons subs = foldr1 mergeSoPMul . map (substSymbol cons subs) . unP

substSymbol :: (Ord c) => c -> SoP c -> Symbol c -> SoP c
substSymbol _ _ s@(I _) = toSoP s
substSymbol cons subst s@(C c)
  | cons == c = subst
  | otherwise = toSoP s

substSymbol cons subst (E b p) = normaliseExp (substSoP cons subst b) (substProduct cons subst p)

substsSubst :: (Ord c) => [Unifier c] -> [Unifier c] -> [Unifier c]
substsSubst s = map subst
  where
    subst sub@(Subst {..}) = sub { sSoP = substsSoP s sSoP }
    subst uni@(Unify {..}) = uni { sLHS = substsSoP s sLHS,
                                   sRHS = substsSoP s sRHS }

data UnifyResult c
  = Win
  | Lose
  | Draw [Unifier c]

unifiers :: (Ord c) => SoP c -> SoP c -> [Unifier c]
unifiers (S [P [C x]]) (S []) = [Subst x (S [P [I 0]])]
unifiers (S []) (S [P [C x]]) = [Subst x (S [P [I 0]])]

unifiers (S [P [C x]]) s = [Subst x s]
unifiers s (S [P [C x]]) = [Subst x s]

-- (z ^ a) ~ (z ^ b) ==> [a := b]
unifiers (S [P [E s1 p1]]) (S [P [E s2 p2]])
  | s1 == s2 = unifiers (toSoP p1) (toSoP p2)

-- (2*e ^ d) ~ (2*e*a*c) ==> [a*c := 2*e ^ (d-1)]
unifiers (S [P [E (S [P s1]) p1]]) (S [P p2])
  | all (`elem` p2) s1
  = let base = s1 `intersect` p2
        diff = p2 \\ s1
    in unifiers (S [P diff]) (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]])

unifiers (S [P p2]) (S [P [E (S [P s1]) p1]])
  | all (`elem` p2) s1
  = let base = s1 `intersect` p2
        diff = p2 \\ s1
    in unifiers (S [P diff]) (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]])

-- (i ^ a) ~ j ==> [a := round (logBase i j)], when `i` and `j` are integers,
unifiers (S [P [E (S [P [I i]]) p]]) (S [P [I j]])
  = case integerLogBase i j of
      Just k  -> unifiers (S [p]) (S [P [I k]])
      Nothing -> []

unifiers  (S [P [I j]]) (S [P [E (S [P [I i]]) p]])
  = case integerLogBase i j of
      Just k  -> unifiers (S [p]) (S [P [I k]])
      Nothing -> []

-- a^d * a^e ~ a^c ==> [c := d + e]
unifiers (S [P [E s1 p1]]) (S [p2]) = case collectBases p2 of
  Just (b:bs,ps) | all (== s1) (b:bs) ->
    unifiers (S [p1]) (S ps)
  _ -> []

unifiers (S [p2]) (S [P [E s1 p1]]) = case collectBases p2 of
  Just (b:bs,ps) | all (== s1) (b:bs) ->
    unifiers (S ps) (S [p1])
  _ -> []

-- (i * a) ~ j ==> [a := div j i]
-- Where 'a' is a variable, 'i' and 'j' are integer literals, and j `mod` i == 0
unifiers (S [P ((I i):ps)]) (S [P [I j]]) =
  case safeDiv j i of
    Just k -> unifiers (S [P ps]) (S [P [I k]])
    _      -> []

unifiers (S [P [I j]]) (S [P ((I i):ps)]) =
  case safeDiv j i of
    Just k -> unifiers (S [P ps]) (S [P [I k]])
    _      -> []

-- (2*a) ~ (2*b) ==> [a := b]
-- unifiers' ct (S [P (p:ps1)]) (S [P (p':ps2)])
--     | p == p'   = unifiers' ct (S [P ps1]) (S [P ps2])
--     | otherwise = []
unifiers (S [P ps1]) (S [P ps2])
    | null psx  = []
    | otherwise = unifiers (S [P ps1'']) (S [P ps2''])
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [I 1]
          | otherwise = ps1'
    ps2'' | null ps2' = [I 1]
          | otherwise = ps2'
    psx  = ps1 `intersect` ps2

-- (2 + a) ~ 5 ==> [a := 3]
unifiers (S ((P [I i]):ps1)) (S ((P [I j]):ps2))
    | i < j     = unifiers (S ps1) (S (P [I (j-i)]:ps2))
    | i > j     = unifiers (S (P [I (i-j)]:ps1)) (S ps2)

-- (a + c) ~ (b + c) ==> [a := b]
unifiers s1@(S ps1) s2@(S ps2) = case splitSoP s1 s2 of
  (s1',s2')
    | s1' /= s1 || s2' /= s1
    -> unifiers s1' s2'
  _ | null psx
    , length ps1 == length ps2
    -> case nub (concat (zipWith (\x y -> unifiers (S [x]) (S [y])) ps1 ps2)) of
        []  -> unifiers' (S ps1) (S ps2)
        [k] -> [k]
        _   -> []
    | null psx
    -> []
  _ -> unifiers (S ps1'') (S ps2'')
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [P [I 0]]
          | otherwise = ps1'
    ps2'' | null ps2' = [P [I 0]]
          | otherwise = ps2'
    psx = ps1 `intersect` ps2

unifiers' :: SoP c -> SoP c -> [Unifier c]
unifiers' _ _ = []

splitSoP :: (Ord c) => SoP c -> SoP c -> (SoP c, SoP c)
splitSoP u v = (lhs, rhs)
  where
    reduced = mergeSoPAdd v (mergeSoPMul u (toSoP (I (-1))))
    (lhs',rhs') = partition neg (unS reduced)
    lhs | null lhs' = S [P [I 0]]
        | otherwise = (mergeSoPMul `on` S) lhs' [P [I (-1)]]
    rhs | null rhs' = S [P [I 0]]
        | otherwise = S rhs'

    neg (P ((I i):_)) = i < 0
    neg _ = False
    
collectBases :: Product c -> Maybe ([SoP c],[Product c])
collectBases = fmap unzip . traverse go . unP
  where
    go (E s1 p1) = Just (s1,p1)
    go _         = Nothing

safeDiv :: Integer -> Integer -> Maybe Integer
safeDiv i j
  | j == 0    = Just 0
  | otherwise = case divMod i j of
                  (k,0) -> Just k
                  _     -> Nothing

integerLogBase :: Integer -> Integer -> Maybe Integer
integerLogBase x y | x > 1 && y > 0 =
  let z1 = integerLogBase' x y
      z2 = integerLogBase' x (y-1)
  in  if z1 == z2
         then Nothing
         else Just z1
integerLogBase _ _ = Nothing

integerLogBase' :: Integer -> Integer -> Integer
integerLogBase' b m = e
  where
    (_, e) = go b

    go pw | m < pw = (m, 0)
    go pw = case go (pw ^ 2) of
              (q, e) | q < pw -> (q, 2 * e)
              (q, e) -> (q `quot` pw, 2 * e + 1)

