-- | Example Carneades Argument Evaluation Structure.
--
-- Demonstrates how to construct and evaluate a CAES using the DSL.
-- For the literate Haskell source with full definitions, see
-- @doc\/ExampleCAES.lhs@.
module Language.Carneades.ExampleCAES where

import Prelude hiding (negate)
import Language.Carneades.CarneadesDSL
import Language.Carneades.Input

-- $example
-- We revisit the murder example from the paper and assume the following:
--
-- * @arguments = {arg1, arg2, arg3}@
-- * @assumptions = {kill, witness, witness2, unreliable2}@
-- * @standard(intent) = beyond-reasonable-doubt@
-- * @standard(x) = scintilla@ for any other proposition @x@
-- * @alpha = 0.4, beta = 0.3, gamma = 0.2@

-- | Argument: kill and intent imply murder.
arg1 :: Argument
arg1 = mkArg ["kill", "intent"] [] "murder"

-- | Argument: witness testimony supports intent (exception: unreliable).
arg2 :: Argument
arg2 = mkArg ["witness"] ["unreliable"] "intent"

-- | Argument: second witness testimony opposes intent (exception: unreliable2).
arg3 :: Argument
arg3 = mkArg ["witness2"] ["unreliable2"] "-intent"

-- | The argument set containing all three arguments.
argSet :: ArgSet
argSet = mkArgSet [arg1, arg2, arg3]

-- | Weight function assigning weights to arguments.
weight :: ArgWeight
weight  arg  |  arg == arg1  = 0.8
weight  arg  |  arg == arg2  = 0.3
weight  arg  |  arg == arg3  = 0.8
weight  _                    = error "no weight assigned"

-- | The assumed propositions.
assumptions :: [PropLiteral]
assumptions = mkAssumptions ["kill", "witness", "witness2","unreliable2"]

-- | The audience combining assumptions and weight function.
audience :: Audience
audience = (assumptions, weight)

-- | Proof standard mapping: intent requires beyond reasonable doubt,
-- everything else requires scintilla.
standard :: PropStandard
standard  (_, "intent")  = BeyondReasonableDoubt
standard  _              = Scintilla

-- | The complete CAES.
caes :: CAES
caes = CAES (argSet, audience, standard)

-- | Applicable arguments for intent.
testAppIntent :: [Argument]
testAppIntent = filter (`applicable` caes) $ getArgs (mkProp "intent") argSet

-- | Applicable arguments for -intent.
testAppNotIntent :: [Argument]
testAppNotIntent = filter (`applicable` caes) $ getArgs (mkProp "-intent") argSet

-- | Applicable arguments for murder.
testAppMurder :: [Argument]
testAppMurder = filter (`applicable` caes) $ getArgs (mkProp "murder") argSet

-- | Applicable arguments for -murder.
testAppNotMurder :: [Argument]
testAppNotMurder = filter (`applicable` caes) $ getArgs (mkProp "-murder") argSet

-- | Whether murder is acceptable.
testMurder  :: Bool
testMurder  = acceptable (mkProp "murder") caes

-- | Whether -murder is acceptable.
testNotMurder  :: Bool
testNotMurder  = acceptable (mkProp "-murder") caes

-- | Parse and display the example CAES file.
parse :: IO ()
parse = do
           input <- readFile "examplecaes.txt"
           (CAES (argSet', (assumps, _weight), standard')) <- case parseCAES input of
               Left err -> fail $ "Parsing error: " ++ show err
               Right res -> return res
           print $ getAllArgs argSet'
           print assumps
           print $ standard' (mkProp "intent")
