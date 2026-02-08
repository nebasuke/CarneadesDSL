module Test.Language.Carneades.Input (tests) where

import Prelude hiding (negate)
import Test.Tasty
import Test.Tasty.HUnit

import Language.Carneades.CarneadesDSL
import Language.Carneades.Input

tests :: TestTree
tests = testGroup "Input"
  [ testGroup "parseCAES"
      [ testCase "parses valid input" $ do
          let input = unlines
                [ "argument arg1 [\"kill\", \"intent\"] [] \"murder\""
                , "weight arg1 0.8"
                , "assumptions [\"kill\", \"intent\"]"
                , "standard \"kill\" scintilla"
                , "standard \"intent\" scintilla"
                ]
          case parseCAES input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (CAES (argSet, (assumps, _), _)) -> do
              length (getAllArgs argSet) @?= 1
              length assumps @?= 2

      , testCase "parses multiple arguments" $ do
          let input = unlines
                [ "argument a1 [\"p\"] [] \"q\""
                , "argument a2 [\"r\"] [\"s\"] \"-q\""
                , "weight a1 0.5"
                , "weight a2 0.6"
                , "assumptions [\"p\", \"r\"]"
                , "standard \"q\" preponderance"
                ]
          case parseCAES input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (CAES (argSet, _, _)) -> do
              length (getAllArgs argSet) @?= 2

      , testCase "parses BeyondReasonableDoubt standard" $ do
          let input = unlines
                [ "argument a1 [\"w\"] [] \"intent\""
                , "weight a1 0.9"
                , "assumptions [\"w\"]"
                , "standard \"intent\" beyond_reasonable_doubt"
                ]
          case parseCAES input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (CAES (_, _, std)) ->
              std (mkProp "intent") @?= BeyondReasonableDoubt

      , testCase "parses constructor-style standard names" $ do
          let input = unlines
                [ "argument a1 [\"x\"] [] \"y\""
                , "weight a1 0.5"
                , "assumptions [\"x\"]"
                , "standard \"y\" Preponderance"
                ]
          case parseCAES input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (CAES (_, _, std)) ->
              std (mkProp "y") @?= Preponderance

      , testCase "handles Haskell-style comments" $ do
          let input = unlines
                [ "-- This is a comment"
                , "argument a1 [\"p\"] [] \"q\""
                , "{- block comment -}"
                , "weight a1 0.5"
                , "assumptions [\"p\"]"
                , "standard \"q\" scintilla"
                ]
          case parseCAES input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (CAES (argSet, _, _)) ->
              length (getAllArgs argSet) @?= 1

      , testCase "rejects malformed input" $ do
          let input = "this is not valid CAES input"
          case parseCAES input of
            Left _  -> return ()
            Right _ -> assertFailure "Expected parse error"
      ]
  , testGroup "round-trip with examplecaes.txt"
      [ testCase "parses example file" $ do
          input <- readFile "examplecaes.txt"
          case parseCAES input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (CAES (argSet, (assumps, _), std)) -> do
              length (getAllArgs argSet) @?= 3
              length assumps @?= 4
              std (mkProp "intent") @?= BeyondReasonableDoubt
              std (mkProp "kill") @?= Scintilla
      ]
  ]
