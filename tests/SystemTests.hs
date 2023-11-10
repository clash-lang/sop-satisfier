import Test.Tasty
import Test.Tasty.HUnit
  ( testCase
  , (@=?)
  )

import SoPSat.SoP
  ( SoP(..)
  , Product(..)
  , Symbol(..)
  , SoPE(..)
  , OrdRel(..)
  , mergeSoPAdd
  , mergeSoPSub
  )
import SoPSat.Satisfier
  ( SolverState
  , evalStatements
  , declare
  , assert
  )


type TestCase   = SolverState String Bool
type TestResult = Maybe Bool

equalityGiven1 :: TestCase
equalityGiven1 =
  let
    one = S [P [I 1]]
    m  = S [P [C "m"]]
    n  = S [P [C "n"]]
    n1 = S [P [C "n1"]]
  in do
    declare (SoPE m (mergeSoPAdd n1 one) EqR)
    assert (SoPE (S [P [C "m"], P [C "n"]]) (S [P [C "n"], P [C "n1"], P [I 1]]) EqR)

runEqualityGiven1 :: TestResult
runEqualityGiven1 = evalStatements equalityGiven1

equalityGiven2 :: TestCase
equalityGiven2 =
  let
    one = S [P [I 1]]
    m  = S [P [C "m"]]
    n  = S [P [C "n"]]
    n1 = S [P [C "n1"]]
  in do
    declare (SoPE m (mergeSoPAdd n1 one) EqR)
    assert (SoPE (S [P [C "m", C "n"]]) (S [P [C "n"], P [C "n", C "n1"]]) EqR)

runEqualityGiven2 :: TestResult
runEqualityGiven2 = evalStatements equalityGiven2

equalityGiven3 :: TestCase
equalityGiven3 =
  let
    one = S [P [I 1]]
    m  = S [P [C "m"]]
    n  = S [P [C "n"]]
    n1 = S [P [C "n1"]]
  in do
    declare (SoPE m (mergeSoPAdd n1 one) EqR)
    assert (SoPE (S [P [E n (P [C "m"])]]) (S [P [C "n", E n (P [C "n1"])]]) EqR)

runEqualityGiven3 :: TestResult
runEqualityGiven3 = evalStatements equalityGiven3

transitivity :: TestCase
transitivity =
  let
    i = S [P [C "i"]]
    j = S [P [C "j"]]
    k = S [P [C "k"]]
  in do
    declare (SoPE i j LeR)
    declare (SoPE j k LeR)
    assert (SoPE i k LeR)

runTransitivity :: TestResult
runTransitivity = evalStatements transitivity

antisymmetryZero :: TestCase
antisymmetryZero =
  let
    z = S [P [I 0]]
    x = S [P [C "x"]]
  in do
    declare (SoPE x z LeR)
    assert (SoPE x z EqR)

runAntisymmetryZero :: TestResult
runAntisymmetryZero = evalStatements antisymmetryZero

antisymmetryNonZero :: TestCase
antisymmetryNonZero = 
  let
    z = S [P [I 42]]
    x = S [P [C "x"]]
  in do
    declare (SoPE x z LeR)
    declare (SoPE z x LeR)
    assert (SoPE x z EqR)

runAntisymmetryNonZero :: TestResult
runAntisymmetryNonZero = evalStatements antisymmetryNonZero

lemma2 :: TestCase
lemma2 =
  let
    o = S [P [I 1]]
    j = S [P [C "j"]]
    n = S [P [C "n"]]
  in do
    declare (SoPE j n LeR)
    declare (SoPE o (mergeSoPSub n j) LeR)
    assert (SoPE (mergeSoPAdd o j) n LeR)

runLemma2 :: TestResult
runLemma2 = evalStatements lemma2

trueInEq :: TestCase
trueInEq =
  let
    x = S [P [C "x"]]
    inEq1 = S [P [E (S [P [I 2]]) (P [C "x"])], P [I 3, E x (P [I 2])], P [I 3]]
    inEq2 = S [P [E x (P [I 3])], P [I (-2), E x (P [I 2])], P [I 4]]
  in
    assert (SoPE inEq2 inEq1 LeR)

runTrueInEq :: TestResult
runTrueInEq = evalStatements trueInEq

falseInEq :: TestCase
falseInEq =
  let
    x = S [P [C "x"]]
    inEq1 = S [P [E (S [P [I 2]]) (P [C "x"])], P [E x (P [I 2])], P [I 3]]
    inEq2 = S [P [E x (P [I 3])], P [I (-2), E x (P [I 2])], P [I 4]]
  in
    assert (SoPE inEq1 inEq2 GeR)

runFalseInEq :: TestResult
runFalseInEq = evalStatements falseInEq

falseInEq2 :: TestCase
falseInEq2 =
  let
    one = S [P [I 1]]
    m   = S [P [C "m"]]
    rp  = S [P [C "rp"]]
  in do
    declare (SoPE one m LeR)
    declare (SoPE m rp LeR)
    assert (SoPE one (mergeSoPSub rp m) LeR)

runFalseInEq2 :: TestResult
runFalseInEq2 = evalStatements falseInEq2

overlapInEq :: TestCase
overlapInEq =
  let
    t = S [P [I 2]]
    f = S [P [I 4]]
    x = S [P [C "x"]]
  in do
    declare (SoPE f x LeR)
    declare (SoPE t x LeR)
    assert (SoPE t x LeR)

runOverlapInEq :: TestResult
runOverlapInEq = evalStatements overlapInEq

eqSubst :: TestCase
eqSubst =
  do
    declare (SoPE
             (S [P [C "x"], P [I 1]])
             (S [P [C "n1"], P [C "m"], P [I 1]])
             EqR)
    declare (SoPE
             (S [P [C "m"]])
             (S [P [C "n1"]])
             EqR)
    declare (SoPE
             (S [P [C "n1"]])
             (S [P [C "n2"], P [C "m1"], P [I 1]])
             EqR)
    assert (SoPE
            (S [P [I 1], P [C "n2"], P [C "m1"]])
            (S [P [C "n1"]])
            EqR)

runEqSubst :: TestResult
runEqSubst = evalStatements eqSubst

eqSubst2 :: TestCase
eqSubst2 =
  do
    declare (SoPE (S [P [I 1]]) (S [P [C "y"]]) LeR)
    declare (SoPE (S [P [I 1], P [C "x"]]) (S [P [I 2,C "y"]]) EqR)
    assert (SoPE (S [P [I (-1)],P [I 2,C "y"]]) (S [P [C "x"]]) EqR)

runEqSubst2 :: TestResult
runEqSubst2 = evalStatements eqSubst2

multistep :: TestCase
multistep =
  do
    declare (SoPE {lhs = S {unS = [P {unP = [I 1]}]}, rhs = S {unS = [P {unP = [C "n_a7oY"]}]}, op = LeR})
    declare (SoPE {lhs = S {unS = [P {unP = [I 2,C "n_a7pf"]}]}, rhs = S {unS = [P {unP = [C "n_a7oY"]}]}, op = EqR})
    r1 <- assert (SoPE {lhs = S {unS = [P {unP = [I (-1)]},P {unP = [I 2,C "n_a7pf"]}]}, rhs = S {unS = [P {unP = [I (-1)]},P {unP = [C "n_a7oY"]}]}, op = EqR})
    r2 <- assert (SoPE {lhs = S {unS = [P {unP = [I 1]}]}, rhs = S {unS = [P {unP = [C "n_a7pf"]}]}, op = LeR})
    return (r1 && r2)

runMultistep :: TestResult
runMultistep = evalStatements multistep

multistep2 :: TestCase
multistep2 =
  do
    declare (SoPE (S [P [C "m"]]) (S [P [C "n1"], P [I 1]]) EqR)
    declare (SoPE (S [P [C "m"], P [C "n"]]) (S [P [C "n2"], P [I 1]]) EqR)
    assert (SoPE (S [P [C "n1"], P [C "n"]]) (S [P [C "n2"]]) EqR)

runMultistep2 :: TestResult
runMultistep2 = evalStatements multistep2

step3 :: TestCase
step3 =
  do
    declare (SoPE (S [P [I 1], P [C "n"]]) (S [P [C "m"]]) EqR)
    declare (SoPE (S [P [I 1], P [C "n1"]]) (S [P [C "m"]]) EqR)
    r1 <- assert (SoPE (S [P [C "n"]]) (S [P [C "n1"]]) EqR)
    r2 <- assert (SoPE (S [P [I 2], P [I 2, C "n"]]) (S [P [I 2, C "m"]]) EqR)
    return (r1 && r2)

runStep3 :: TestResult
runStep3 = evalStatements step3

implication :: TestCase
implication =
  do
    declare (SoPE (S [P [I 2]]) (S [P [E (S [P [I 2]]) (P [C "n"]), E (S [P [I 2]]) (P [C "m"])]]) LeR)
    assert (SoPE (S [P [I 2]]) (S [P [E (S [P [I 2]]) (P [C "m"]), E (S [P [I 2]]) (P [C "n"])]]) LeR)

runImplication :: TestResult
runImplication = evalStatements implication

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lib-tests"
  [ testGroup "Equality tests"
    [ testGroup "True"
      [ testCase "m = n1 + 1 implies n + m = n + n1 + 1" $
        Just True @=? runEqualityGiven1
      , testCase "m = n1 + 1 implies n * m = n + n * n1" $
        Just True @=? runEqualityGiven2
      , testCase "m = n1 + 1 implies n^m = n*n^n1" $
        Just True @=? runEqualityGiven3
      , testCase "n + 1 = n1 + m + 1 and m = n1 and n1 = n2 + m1 + 1 implies 1 + n2 + m1 = n1" $
        Just True @=? runEqSubst
      , testCase "1 <= y and x + 1 = 2 * y implies 2 * y - 1 = x" $
        Just True @=? runEqSubst2
      , testCase "9 = x + x + x" $
        Just True @=?
        evalStatements (assert
                        (SoPE (S (replicate 3 (P [C "x"]))) (S [P [I 9]]) EqR))
      , testCase "6 = 2 * y + 4" $
        Just True @=?
        evalStatements (assert
                        (SoPE (S [P [I 2, C "x"], P [I 4]]) (S [P [I 6]]) EqR))
      , testCase "Combined: 1 <= m and 2 * n = m implies 2 * n - 1 = m - 2 and 1 <= m" $
        Just True @=? runMultistep
      , testCase "Multistep: m = n1 + 1 and m + n = n2 + 1 implies n1 + n = n2" $
        Just True @=? runMultistep2
      , testCase "1 + a = c and 1 + b = c implies a = b and 2 + 2 * a = 2 * c" $
        Just True @=? runStep3
      ]
    , testGroup "False"
      [ testCase "x + 2 /= x + 3" $
        Just False @=?
        evalStatements (assert
                        (SoPE (S [P [C "x"], P [I 2]]) (S [P [C "x"], P [I 3]]) EqR))
      , testCase "8 /= x + x + x" $
        Just False @=?
        evalStatements (assert
                        (SoPE (S (replicate 3 (P [C "x"]))) (S [P [I 8]]) EqR))
      , testCase "7 /= 2*y+4" $
        Just False @=?
        evalStatements (assert
                        (SoPE (S [P [I 2, C "x"], P [I 4]]) (S [P [I 7]]) EqR))
      ]
    ]
  , testGroup "Inequality tests"
    [ testGroup "True"
      [ testCase "Transitivity: i <= j and j <= k implies i <= k" $
        Just True @=? runTransitivity
      , testCase "Antisymmetry with zero: x is Natural and x <= 0 implies x = 0" $
        Just True @=? runAntisymmetryZero
      , testCase "Antisymmetry with non-zero: x <= 5 and x >= 5 implies x = 5" $
        Just True @=? runAntisymmetryNonZero
      , testCase "Strongly greater: j <= n and 1 <= n - j imples 1 + j <= n" $
        Just True @=? runLemma2
      , testCase "Composite function: x^3-2x^2+4<=2^x+3x^2+3" $
        Just True @=? runTrueInEq
      , testCase "Overlapping ranges: 4 <= x implies 2 <= x" $
        Just True @=? runOverlapInEq
      , testGroup "Trivial"
        [ testCase "a <= a + 1" $
          Just True @=?
          evalStatements (assert
                          (SoPE (S [P [C "a"]]) (S [P [C "a"], P [I 1]]) LeR))
        , testCase "1 <= 2^a" $
          Just True @=?
          evalStatements (assert
                          (SoPE (S [P [I 1]]) (S [P [E (S [P [I 2]]) (P [C "a"])]]) LeR))
        , testCase "2 <= 2^(n + m) implies 2 <= 2^(m + n)" $
          Just True @=? runImplication
        ]
      ]
    , testGroup "False"
      [ testCase "Composite function x^3-2x^2+4<=2^x+x^2+3" $
        Just False @=? runFalseInEq
      , testCase "1 <= m and m <= rp implies 1 <= rp - m" $
        Just False @=? runFalseInEq2
      , testCase "4a <= 2a" $
        Just False @=?
        evalStatements (assert
                        (SoPE (S [P [I 4, C "a"]]) (S [P [I 2, C "a"]]) LeR))
      ]
    ]
  , testGroup "Ranges"
    [ -- TODO: Add test cases for range narrowing consistency
    ]
  ]
