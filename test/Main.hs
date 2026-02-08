module Main (main) where

import Test.Tasty

import qualified Test.Language.Carneades.CarneadesDSL
import qualified Test.Language.Carneades.Input

main :: IO ()
main = defaultMain $ testGroup "CarneadesDSL"
  [ Test.Language.Carneades.CarneadesDSL.tests
  , Test.Language.Carneades.Input.tests
  ]
