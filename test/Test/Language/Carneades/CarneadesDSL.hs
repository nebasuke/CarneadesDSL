module Test.Language.Carneades.CarneadesDSL (tests) where

import Prelude hiding (negate)
import Test.Tasty
import Test.Tasty.HUnit

import Language.Carneades.CarneadesDSL
import Language.Carneades.ExampleCAES

tests :: TestTree
tests = testGroup "CarneadesDSL"
  [ testGroup "mkProp"
      [ testCase "positive literal" $
          mkProp "kill" @?= (True, "kill")
      , testCase "negative literal" $
          mkProp "-intent" @?= (False, "intent")
      , testCase "double negation" $
          mkProp "--x" @?= (True, "x")
      ]
  , testGroup "negate"
      [ testCase "negate positive" $
          negate (True, "p") @?= (False, "p")
      , testCase "negate negative" $
          negate (False, "p") @?= (True, "p")
      ]
  , testGroup "mkArg"
      [ testCase "constructs argument" $ do
          let a = mkArg ["kill", "intent"] [] "murder"
          let Arg (prems, excs, c) = a
          length prems @?= 2
          excs @?= []
          c @?= (True, "murder")
      , testCase "negative conclusion" $ do
          let a = mkArg ["witness2"] ["unreliable2"] "-intent"
          let Arg (_, _, c) = a
          c @?= (False, "intent")
      ]
  , testGroup "mkArgSet"
      [ testCase "acyclic set is not cyclic" $
          checkCycle argSet @?= False
      , testCase "retrieves arguments for prop" $ do
          let args = getArgs (mkProp "murder") argSet
          length args @?= 1
      , testCase "no arguments for unknown prop" $ do
          let args = getArgs (mkProp "unknown") argSet
          args @?= []
      ]
  , testGroup "applicability (ExampleCAES)"
      [ testCase "arg2 is applicable for intent" $
          testAppIntent @?= [arg2]
      , testCase "no applicable args for -intent" $
          testAppNotIntent @?= []
      , testCase "no applicable args for murder (intent not accepted)" $
          testAppMurder @?= []
      , testCase "no applicable args for -murder" $
          testAppNotMurder @?= []
      ]
  , testGroup "acceptability (ExampleCAES)"
      [ testCase "murder is not acceptable" $
          testMurder @?= False
      , testCase "-murder is not acceptable" $
          testNotMurder @?= False
      ]
  , testGroup "proof standards"
      [ testCase "scintilla: at least one applicable arg" $ do
          -- intent has applicable arg2, so scintilla should pass
          let result = scintilla (mkProp "intent") caes
          result @?= True
      , testCase "scintilla: no applicable arg fails" $ do
          -- -intent has no applicable args (unreliable2 is an exception)
          let result = scintilla (mkProp "-intent") caes
          result @?= False
      , testCase "beyond reasonable doubt: weight too low" $ do
          -- intent's arg2 has weight 0.3 < alpha=0.4
          let result = beyond_reasonable_doubt (mkProp "intent") caes
          result @?= False
      ]
  , testGroup "convenience functions"
      [ testCase "getAllArgs returns all arguments" $ do
          let allArgs = getAllArgs argSet
          length allArgs @?= 3
      , testCase "getProps returns all propositions" $ do
          let props = getProps argSet
          -- Should have murder, -murder, intent, -intent, kill, witness, witness2, unreliable, unreliable2
          assertBool "at least 5 props" (length props >= 5)
      , testCase "applicableArgs" $ do
          let appArgs = applicableArgs caes
          -- Only arg2 (witness -> intent) is applicable
          appArgs @?= [arg2]
      , testCase "acceptableProps returns empty for this CAES" $ do
          let accProps = acceptableProps caes
          -- kill and witness are assumptions but not in the graph as conclusions
          -- intent fails BeyondReasonableDoubt, murder fails since intent not acceptable
          accProps @?= []
      ]
  ]
