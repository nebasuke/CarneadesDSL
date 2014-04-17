%include arg-preamble.fmt

\begin{code}
module Language.Carneades.ExampleCAES where

import Prelude hiding (negate)
import Language.Carneades.CarneadesDSL
import Language.Carneades.Input
import System.Exit
import Control.Monad (when)
\end{code}



\subsection{Implementing a CAES}

This subsection shows how an argumentation theorist given the
Carneades DSL developed in this section quickly and at a high level of
abstraction can implement a Carneades argument evaluation structure
and evaluate it as well. We revisit the arguments from Section
\ref{sec:background} and assume the following:

\begin{align*}
\mathit{arguments} &= \{\mathit{arg1}, \mathit{arg2}, \mathit{arg3} \}, \\
\mathit{assumptions} &= \{\mathit{kill}, \mathit{witness}, \mathit{witness2}, \mathit{unreliable2} \},\\
\mathit{standard(intent)} &= \mathit{beyond}\textit{-}\mathit{reasonable}\textit{-}\mathit{doubt}, \\
\mathit{standard(x)} &= \mathit{scintilla},\ \textrm{for any other proposition x}, \\
\alpha &= 0.4,\ \beta = 0.3,\ \gamma = 0.2.
\end{align*}

Note that since alpha, beta and gamma are assumed they are global, they are predefined in |CarneadesDSL.lhs|.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Start example code%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{spec}
alpha, beta, gamma :: Double
alpha  =  0.4
beta   =  0.3
gamma  =  0.2
\end{spec}


Arguments and the argument graph are constructed by calling |mkArg| and
|mkArgSet| respectively:
\begin{code}
arg1, arg2, arg3 :: Argument 
arg1 = mkArg ["kill", "intent"] [] "murder"
arg2 = mkArg ["witness"] ["unreliable"] "intent"
arg3 = mkArg ["witness2"] ["unreliable2"] "-intent"

argSet :: ArgSet
argSet = mkArgSet [arg1, arg2, arg3]
\end{code}

The audience is implemented by defining the |weight| function and calling
|mkAssumptions| on the propositions which are to be assumed. The audience is
just a pair of these:


\begin{code}
weight :: ArgWeight
weight  arg  |  arg == arg1  = 0.8
weight  arg  |  arg == arg2  = 0.3
weight  arg  |  arg == arg3  = 0.8
weight  _                    = error "no weight assigned"

assumptions :: [PropLiteral]
assumptions = mkAssumptions ["kill", "witness", "witness2","unreliable2"] 

audience :: Audience
audience = (assumptions, weight) 
\end{code}

Finally, after assigning proof standards in the |standard| function, we form
the CAES from the argument graph, audience and function |standard|:
\begin{code}
standard :: PropStandard 
standard  (_, "intent")  = BeyondReasonableDoubt 
standard  _              = Scintilla 

caes :: CAES 
caes = CAES (argSet, audience, standard)
\end{code}

We can now try out the argumentation structure. 

\begin{spec}
getAllArgs argSet
 > [  ["witness2"]       ~["unreliable2"]   =>  "-intent",
      ["witness"]        ~["unreliable"]    =>  "intent",
      ["kill","intent"]  ~[]                =>  "murder"]
\end{spec}

Then, as expected, there are no applicable arguments for $\mathit{-intent}$, 
since $\mathit{unreliable2}$ is an exception, but there is an applicable 
argument for $\mathit{intent}$, namely $\mathit{arg2}$:


\begin{spec}
filter (`applicable` caes) $ getArgs (mkProp "intent") argSet
 > [["witness"]=>"intent"]

filter (`applicable` caes) $ getArgs (mkProp "-intent") argSet
 >  []
\end{spec}

Despite the applicable argument $\mathit{arg2}$ for $\mathit{intent}$,
$\mathit{murder}$ should not be acceptable, because the weight of
$\mathit{arg2} < \alpha$. However, note that we can't reach the opposite
conclusion either:

\begin{spec}
acceptable (mkProp "murder") caes
 > False
acceptable (mkProp "-murder") caes
 > False
\end{spec}

As a further extension, one could for example imagine giving an
argumentation theorist the means to see a trace of the derivation of
acceptability. It would be straightforward to add further primitives
to the DSL and keeping track of intermediate results for
acceptability and applicability to achieve this.

\begin{code}
testAppIntent :: [Argument]
testAppIntent = filter (`applicable` caes) $ getArgs (mkProp "intent") argSet        

testAppNotIntent :: [Argument]
testAppNotIntent = filter (`applicable` caes) $ getArgs (mkProp "-intent") argSet        

testAppMurder :: [Argument]
testAppMurder = filter (`applicable` caes) $ getArgs (mkProp "murder") argSet        

testAppNotMurder :: [Argument]
testAppNotMurder = filter (`applicable` caes) $ getArgs (mkProp "-murder") argSet        

testMurder  :: Bool
testMurder  = acceptable (mkProp "murder") caes

testNotMurder  :: Bool
testNotMurder  = acceptable (mkProp "-murder") caes
\end{code}

Assuming a file examplecaes.txt with the following input:


argument arg1 ["kill", "intent"] [ ] "murder"
argument arg2 ["witness" ] ["unreliable"] "intent"
argument arg3 ["witness2"] ["unreliable2"] "-intent"

weight arg1 0.8
weight arg2 0.3
weight arg3 0.8

assumptions ["kill", "witness", "witness2", "unreliable2"]

-- Haskell style commments are allowed.

{- also valid for standards: 
   standard "intent" BeyondReasonableDoubt -}

standard "kill" scintilla
standard "intent" beyond_reasonable_doubt


\begin{code}
parse :: IO ()
parse = do 
           input <- readFile "examplecaes.txt"
           argSet <- case (parseCAES input) of 
               Left err -> putStrLn "Parsing error: " >> print err >> exitWith (ExitFailure 1)
               Right (CAES (argSet, _, _)) -> return argSet
           print $ getAllArgs argSet
\end{code}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%End example code%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

