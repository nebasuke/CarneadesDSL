-- | An implementation and DSL for the Carneades argumentation model.
--
-- See \"Haskell Gets Argumentative\" in the Proceedings of Symposium on
-- Trends in Functional Programming (TFP 2012) by Bas van Gijzel and
-- Henrik Nilsson.
--
-- For the literate Haskell source with full definitions, see
-- @doc\/CarneadesDSL.lhs@.
module Language.Carneades.CarneadesDSL where

import Language.Carneades.Cyclic

import Prelude hiding (negate)

import Data.Graph.Inductive
import Data.Map (Map)
import Data.List (nub)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (fromJust)

-- $arguments
-- In Carneades all logical formulae are literals in propositional logic;
-- i.e., all propositions are either positive or negative atoms. Taking
-- atoms to be strings suffices, and propositional literals can then be
-- formed by pairing this atom with a 'Bool' to denote whether it is
-- negated or not.

-- | A propositional literal is a pair of a polarity and a name.
type PropLiteral = (Bool, String)

-- | Negate a propositional literal.
negate :: PropLiteral -> PropLiteral
negate (b, x) = (not b, x)

-- | An argument is a tuple of premises, exceptions, and a conclusion.
-- Arguments are considered equal if their premises, exceptions and
-- conclusion are equal (comparing lists as sets).
newtype Argument = Arg ([PropLiteral], [PropLiteral], PropLiteral)
 deriving Ord

-- Manual Eq instance for set equality on premises and exceptions
instance Eq Argument where
 (Arg (prems, excs, c)) == (Arg (prems', excs', c'))
    =  Set.fromList prems == Set.fromList prems'  &&
       Set.fromList excs == Set.fromList excs'    &&
       c == c'

-- | Show a propositional literal as a string, prefixing negative
-- literals with @-@.
showProp :: PropLiteral -> String
showProp (True, c)   = c
showProp (_    , c)  = '-' : c

instance Show Argument where
 show (Arg (prems, excs, (True, c)))   = show (map showProp prems) ++ ' ' : '~' : show (map showProp excs) ++ "=>" ++ show c
 show (Arg (prems, excs, (_    , c)))  = show (map showProp prems) ++ ' ' : '~' : show (map showProp excs) ++ "=>" ++ show ('-' : c)

-- $caes
-- A Carneades Argument Evaluation Structure ('CAES') is a triple of an
-- acyclic set of arguments, an audience, and a mapping from propositions
-- to proof standards.

-- | An acyclic set of arguments represented as an FGL graph.
type ArgSet = Gr (PropLiteral, [Argument]) ()

-- | A Carneades Argument Evaluation Structure.
newtype CAES = CAES (ArgSet, Audience, PropStandard)

-- | An audience is a pair of assumptions and a weight function.
type Audience = (Assumptions, ArgWeight)

-- | A list of assumed propositional literals.
type Assumptions = [PropLiteral]

-- | A function mapping arguments to weights in the range @[0,1]@.
type ArgWeight = Argument -> Weight

-- | A weight is a 'Double'.
type Weight = Double

-- | A mapping from propositions to proof standard names.
type PropStandard = PropLiteral -> PSName

-- | Names of the five predefined proof standards.
data PSName = Scintilla
  | Preponderance | ClearAndConvincing
  | BeyondReasonableDoubt | DialecticalValidity
 deriving (Show, Eq)

-- | A proof standard decides, given a proposition and a CAES, whether the
-- proposition is acceptable.
type ProofStandard = PropLiteral -> CAES -> Bool

-- | A named proof standard, with equality based on the name.
newtype ProofStandardNamed = P (String, PropLiteral -> CAES -> Bool)
instance Eq ProofStandardNamed where
 P (l1, _) == P (l2, _) = l1 == l2

-- $evaluation
-- Two concepts central to evaluation: /applicability/ of arguments and
-- /acceptability/ of propositions.

-- | An argument is applicable in a CAES when all premises are assumed or
-- acceptable, and all exceptions are neither assumed nor acceptable.
applicable :: Argument -> CAES -> Bool
applicable  (Arg (prems, excns, _))
            caes@(CAES (_, (assumptions, _), _))
  = and  $  [  p `elem` assumptions ||
             (  negate p `notElem` assumptions &&
                p `acceptable` caes)  |  p <- prems  ]
            ++
            [  (e `notElem` assumptions) &&
             (  negate e `elem` assumptions ||
                not (e `acceptable` caes))  |  e <- excns  ]

-- | A proposition is acceptable in a CAES when it satisfies its
-- associated proof standard.
acceptable :: PropLiteral -> CAES -> Bool
acceptable c caes@(CAES (_, _, standard))
  = c `s` caes
  where s = psMap $ standard c

-- $proofstandards
-- Carneades predefines five proof standards.

-- | Scintilla of evidence: at least one applicable argument pro.
scintilla :: ProofStandard
scintilla p caes@(CAES (g, _, _))
 = any (`applicable` caes) (getArgs p g)

-- | Maximum weight among applicable arguments.
maxWeightApplicable :: [Argument] -> CAES -> Weight
maxWeightApplicable as caes@(CAES (_, (_, argWeight), _))
 = foldl max 0 [argWeight a | a <- as, a `applicable` caes]

-- | Maximum weight of applicable arguments pro a proposition.
maxWeightPro :: PropLiteral -> CAES -> Weight
maxWeightPro p caes@(CAES (g, _, _))
 = maxWeightApplicable (getArgs p g) caes

-- | Maximum weight of applicable arguments con a proposition.
maxWeightCon :: PropLiteral -> CAES -> Weight
maxWeightCon p caes@(CAES (g, _, _))
 = maxWeightApplicable (getArgs (negate p) g) caes

-- | Preponderance: max weight pro exceeds max weight con.
preponderance :: ProofStandard
preponderance p caes = maxWeightPro p caes > maxWeightCon p caes

-- | Clear and convincing evidence: preponderance plus minimum
-- thresholds on weight and difference.
clear_and_convincing :: ProofStandard
clear_and_convincing p caes
 =  (mwp > alpha) && (mwp - mwc > beta)
  where
    mwp  =  maxWeightPro p caes
    mwc  =  maxWeightCon p caes

-- | Beyond reasonable doubt: clear and convincing plus max weight
-- con must be below gamma.
beyond_reasonable_doubt :: ProofStandard
beyond_reasonable_doubt p caes
 = clear_and_convincing p caes && (maxWeightCon p caes < gamma)

-- | Dialectical validity: at least one applicable argument pro and
-- no applicable arguments con.
dialectical_validity :: ProofStandard
dialectical_validity p caes
  = scintilla p caes && not (scintilla (negate p) caes)

-- | Map proof standard names to their implementation.
psMap :: PSName -> ProofStandard
psMap Scintilla = scintilla
psMap Preponderance = preponderance
psMap ClearAndConvincing = clear_and_convincing
psMap BeyondReasonableDoubt = beyond_reasonable_doubt
psMap DialecticalValidity = dialectical_validity

-- $convenience
-- Functions to facilitate construction of propositions, arguments,
-- argument sets and assumptions.

-- | Retrieve all arguments from an argument set.
getAllArgs :: ArgSet -> [Argument]
getAllArgs g = nub $ concatMap (snd . snd) (labNodes g)

-- | Retrieve all propositions from an argument set.
getProps :: ArgSet -> [PropLiteral]
getProps g = map (fst . snd) (labNodes g)

-- | Retrieve all applicable arguments from a CAES.
applicableArgs :: CAES -> [Argument]
applicableArgs c@(CAES (argSet, _, _)) = filter (`applicable` c) (getAllArgs argSet)

-- | Retrieve all non-applicable arguments from a CAES.
nonApplicableArgs :: CAES -> [Argument]
nonApplicableArgs c@(CAES (argSet, _, _)) = filter (not . (`applicable` c)) (getAllArgs argSet)

-- | Retrieve all acceptable propositions from a CAES.
acceptableProps :: CAES  -> [PropLiteral]
acceptableProps c@(CAES (argSet, _, _)) = filter (`acceptable` c) (getProps argSet)

-- | Retrieve all non-acceptable propositions from a CAES.
nonAcceptableProps :: CAES  -> [PropLiteral]
nonAcceptableProps c@(CAES (argSet, _, _)) = filter (not . (`acceptable` c)) (getProps argSet)

contextP :: PropLiteral -> AGraph -> [Context (PropLiteral, [Argument]) ()]
contextP p = gsel (\ (_, _, a, _) -> fst a == p)

-- | Retrieve the arguments for a specific proposition from an argument set.
getArgs :: PropLiteral -> AGraph -> [Argument]
getArgs p g
  =  case contextP p g of
       []                          -> []
       ((_, _, (_, args), _) : _)  -> args

-- $graph
-- Graph construction internals.

-- | Synonym for 'ArgSet'.
type AGraph = ArgSet

-- | A labelled node in the argument graph.
type PropNode = LNode (PropLiteral, [Argument])

-- | An argument graph paired with a map from propositions to node numbers.
type AssociatedGraph = (AGraph, Map PropLiteral Node)

-- | Construct an acyclic argument set from a list of arguments.
mkArgSet :: [Argument] -> ArgSet
mkArgSet = mkArgGraph

mkArgGraph :: [Argument] -> AGraph
mkArgGraph = fst . foldr addArgument (empty, Map.empty)

addArgument :: Argument -> AssociatedGraph -> AssociatedGraph
addArgument arg@(Arg (prem, exc, c)) gr  =
  let  deps             =  prem ++ exc
       (gr',  nodeNr)   =  addArgument' arg gr
       (gr'', nodeNr')  =  addNode (negate c) gr'
  in addEdges nodeNr' deps $ addEdges nodeNr deps gr''

addToContext :: Argument -> (Context (PropLiteral, [Argument]) (), AGraph) -> AGraph
addToContext arg ((adjb, n, (p, args), adja), g') = (adjb, n, (p, arg:args), adja) & g'

unsafeMatch :: Graph gr => Node -> gr a b -> (Context a b, gr a b)
unsafeMatch n g = mapFst fromJust $ match n g

addArgument' :: Argument -> AssociatedGraph -> (AssociatedGraph, Node)
addArgument' arg@(Arg (_, _, c)) (g, m)
 = case Map.lookup c m of
       Nothing  ->  ((insNode (nodeNr, (c, [arg])) g,
                       Map.insert c nodeNr m),
                         nodeNr)
       Just n   ->  ((addToContext arg (unsafeMatch n g),
                       m),
                         n)
  where nodeNr = Map.size m + 1

addNode :: PropLiteral -> AssociatedGraph -> (AssociatedGraph, Node)
addNode p gr@(g,m)
 =  case Map.lookup p m of
       Nothing -> ((insNode (nodeNr, (p, [])) g, Map.insert p nodeNr m), nodeNr)
       Just n  -> (gr, n)
    where nodeNr = Map.size m + 1

addEdges :: Node -> [PropLiteral] -> AssociatedGraph -> AssociatedGraph
addEdges n ps (g, m) = addEdges' n (map (fromJust . flip Map.lookup m') ps)  (g', m')
 where  nodeNr    = Map.size m + 1
        newProps  = filter ( (== Nothing) . flip Map.lookup m) ps
        g'        = insNodes (propsToNodes newProps nodeNr) g
        m'        = Map.union m . Map.fromList $ zip newProps [nodeNr..]

addEdges' :: Node -> [Node] -> AssociatedGraph -> AssociatedGraph
addEdges' c ps (g, m) = (insEdges edges' g, m)
 where  edges' = map (genEdge c) ps
        genEdge k l = (k, l, ())

propsToNodes :: [PropLiteral] -> Node -> [PropNode]
propsToNodes ps n = zip [n..] (map (\ p -> (p, [])) ps)

-- | Check whether an argument graph is cyclic.
checkCycle :: AGraph -> Bool
checkCycle = cyclic

-- | Construct a 'PropLiteral' from a string. A leading @-@ denotes
-- a negative literal.
mkProp :: String -> PropLiteral
mkProp ('-':s)  = mapFst not (mkProp s)
mkProp s        = (True, s)

-- | Construct a list of assumptions from a list of strings.
mkAssumptions :: [String] -> [PropLiteral]
mkAssumptions = map mkProp

-- | Construct an 'Argument' from lists of premise, exception, and
-- conclusion strings.
mkArg :: [String] -> [String] -> String -> Argument
mkArg ps es c = Arg (map mkProp ps, map mkProp es, mkProp c)

-- | Globally predefined alpha, beta and gamma thresholds for proof
-- standards.
alpha, beta, gamma :: Double
alpha  =  0.4
beta   =  0.3
gamma  =  0.2
