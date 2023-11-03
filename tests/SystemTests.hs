import Test.Tasty
import Test.Tasty.HUnit
  ( testCase
  , (@=?)
  )

import SoP
  ( SoP(..)
  , Product(..)
  , Symbol(..)
  , SoPE(..)
  , OrdRel(..)
  , mergeSoPAdd
  , mergeSoPSub
  )
import MyLib (SolverState, evalStatements, declare, assert)

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

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lib-tests"
  [ testGroup "Equality tests"
    [ testGroup "True"
      [ testCase "m = n1 + 1 implies n + m = n + n1 + 1" $
        runEqualityGiven1 @=? Just True
      , testCase "m = n1 + 1 implies n * m = n + n * n1" $
        runEqualityGiven2 @=? Just True
      , testCase "m = n1 + 1 implies n^m = n*n^n1" $
        runEqualityGiven3 @=? Just True
      ]
    , testGroup "False"
      [ testCase "x + 2 == x + 3" $
        evalStatements (assert
                        (SoPE (S [P [C "x"], P [I 2]]) (S [P [C "x"], P [I 3]]) EqR))
        @=? Just False
      ]
    ]
  , testGroup "Inequality tests"
    [ testGroup "True"
      [ testCase "Transitivity: i <= j and j <= k implies i <= k" $
        runTransitivity @=? Just True
      , testCase "Antisymmetry with zero: x is Natural and x <= 0 implies x = 0" $
        runAntisymmetryZero @=? Just True
      , testCase "Antisymmetry with non-zero: x <= 5 and x >= 5 implies x = 5" $
        runAntisymmetryNonZero @=? Just True
      , testCase "Strongly greater: j <= n and 1 <= n - j imples 1 + j <= n" $
        runLemma2 @=? Just True
      , testCase "Composite function: x^3-2x^2+4<=2^x+3x^2+3" $
        runTrueInEq @=? Just True
      , testCase "Overlapping ranges: 4 <= x implies 2 <= x" $
        runOverlapInEq @=? Just True
      , testGroup "Trivial"
        [ testCase "a <= a + 1" $
          evalStatements (assert
                          (SoPE (S [P [C "a"]]) (S [P [C "a"], P [I 1]]) LeR))
          @=? Just True
        , testCase "1 <= 2^a" $
          evalStatements (assert
                          (SoPE (S [P [I 1]]) (S [P [E (S [P [I 2]]) (P [C "a"])]]) LeR))
          @=? Just True
        ]
      ]
    , testGroup "False"
      [ testCase "Composite function x^3-2x^2+4<=2^x+x^2+3" $
        runFalseInEq @=? Just False
      , testCase "1 <= m and m <= rp implies 1 <= rp - m" $
        runFalseInEq2 @=? Just False
      , testCase "4a <= 2a" $
        evalStatements (assert
                        (SoPE (S [P [I 4, C "a"]]) (S [P [I 2, C "a"]]) LeR))
        @=? Just False
      ]
    ]
  , testGroup "Ranges"
    [ -- TODO: Add test cases for range narrowing consistency
    ]
  ]
