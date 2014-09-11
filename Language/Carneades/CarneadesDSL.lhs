%include arg-preamble.fmt

\begin{code}
module Language.Carneades.CarneadesDSL where

import Language.Carneades.Cyclic

import Prelude hiding (negate)

import Data.Graph.Inductive
import Data.Map (Map)
import Data.List(nub)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (fromJust)
\end{code}


\subsection{Arguments}
As our ultimate goal is a DSL for argumentation theory, we strive for a
realisation in Haskell that mirrors the mathematical model of Carneades
argumentation framework as closely as possible. Ideally, there would be little
more to a realisation than a transliteration. We will thus proceed by
stating the central definitions of Carneades along with our realisation
of them in Haskell. 

\begin{definition}[Arguments]
\label{def:carneadesargs}
Let $\mathcal{L}$ be a propositional language. An \emph{argument} is a
tuple $\langle P, E, c \rangle$ where $P \subset \mathcal{L}$ are its
\emph{premises}, $E \subset \mathcal{L}$ with $P \cap E = \emptyset$
are its \emph{exceptions} and $c \in \mathcal{L}$ is its
\emph{conclusion}. For simplicity, all members of $\mathcal{L}$ 
must be literals, i.e. either an atomic proposition or a negated
atomic proposition.  
An argument is said to be \emph{pro} its conclusion $c$ (which may be
a negative atomic proposition) and \emph{con} the negation of $c$.
\end{definition}

In Carneades all logical formulae are literals in propositional logic;
i.e., all propositions are either positive or negative atoms. Taking
atoms to be strings suffice in the following, and propositional literals can
then be formed by pairing this atom with a Boolean to denote whether
it is negated or not: 
\begin{code} 
type PropLiteral = (Bool, String)
\end{code}
We write $\overline{p}$ for the negation of a literal $p$. The realisation
is immediate:
\begin{code}
negate :: PropLiteral -> PropLiteral 
negate (b, x) = (not b, x)
\end{code}

We chose to realise an \emph{argument} as a newtype (to allow a manual Eq instance)
containing a tuple of two lists of propositions, its \emph{premises} and its 
\emph{exceptions}, and a proposition that denotes the \emph{conclusion}: 
\begin{code}
newtype Argument = Arg ([PropLiteral], [PropLiteral], PropLiteral)
 deriving Ord 
\end{code}

Arguments are considered equal if their premises, exceptions and
conclusion are equal; thus arguments are identified by their logical
content. The equality instance for |Argument| (omitted for brevity) takes
this into account by comparing the lists as sets.

\begin{code}
--Manual Eq instance for set equality on premises and exceptions
instance Eq Argument where
 (Arg (prems, excs, c)) == (Arg (prems', excs', c')) 
    =  Set.fromList prems == Set.fromList prems'  && 
       Set.fromList excs == Set.fromList excs'    && 
       c == c'

showProp :: PropLiteral -> String
showProp (True, c)   = c
showProp (_    , c)  = '-' : c

instance Show Argument where 
 show (Arg (prems, excs, (True, c)))   = show (map showProp prems) ++ ' ' : '~' : show (map showProp excs) ++ "=>" ++ show c
 show (Arg (prems, excs, (_    , c)))  = show (map showProp prems) ++ ' ' : '~' : show (map showProp excs) ++ "=>" ++ show ('-' : c)
\end{code}


A set of arguments determines how propositions depend on each other.
Carneades requires that there are no cycles among these dependencies. 
Following Brewka and Gordon~\cite{Brewka10a}, we use a dependency
graph to determine acyclicity of a set of arguments.

\begin{definition}[Acyclic set of arguments]
\label{def:carneadesacyclic}
A set of \emph{arguments} is \emph{acyclic} iff its corresponding
dependency graph is acyclic. The corresponding dependency graph has a
node for every literal appearing in the set of arguments. A node $p$
has a link to node $q$ whenever $p$ depends on $q$ in the sense that
there is an argument pro or con $p$ that has $q$ or $\overline{q}$ in
its set of premises or exceptions.
\end{definition}

Our realisation of a set of arguments is considered abstract for DSL
purposes, only providing a check for acyclicity and a function to
retrieve arguments pro a proposition. We use FGL \cite{Erwig2001} to
implement the dependency graph, forming nodes for propositions and edges
for the dependencies. For simplicity, we opt to keep the graph
also as the representation of a set of arguments.


\begin{code}
-- Note that for practical purposes we do not need to know the following 
-- implementation but can use the abstraction further below
type ArgSet = Gr (PropLiteral, [Argument]) ()
\end{code}


\begin{spec}
-- abstraction of ArgSet and the operating functions on it
type ArgSet = ...

getArgs     :: PropLiteral -> ArgSet -> [Argument]  
checkCycle  :: ArgSet -> Bool
\end{spec}


\subsection{Carneades Argument Evaluation Structure}

The main structure of the argumentation model is called a Carneades
Argument Evaluation Structure (CAES):
\begin{definition}[Carneades Argument Evaluation Structure (CAES)] A
\emph{Carneades Argument Evaluation Structure} (CAES) is a triple
\[
\langle arguments, audience, standard \rangle
\]
where $arguments$ is an acyclic set of arguments, $audience$ is an audience as
defined below (Def.~\ref{def:carneadesaudience}), and \emph{standard} is a
total function mapping each proposition to to its specific proof standard. 
\end{definition}
Note that propositions may be associated with \emph{different} proof
standards. This is considered a particular strength of the Carneades
framework. The transliteration into Haskell is almost immediate%
\footnote{Note that we use a newtype to prevent a cycle in the type
definitions.}:
\begin{code}
newtype CAES = CAES (ArgSet, Audience, PropStandard)
\end{code}

\begin{definition}[Audience]
\label{def:carneadesaudience}
Let $\mathcal{L}$ be a propositional language. An \emph{audience} is a
tuple $\langle$\emph{assumptions}, \emph{weight}$\rangle$, where
$assumptions \subset \mathcal{L}$ is a propositionally consistent set of
literals (i.e., not containing both a literal and its negation) assumed
to be acceptable by the audience and \emph{weight} is a function mapping
arguments to a real-valued weight in the range $[0,1]$.
\end{definition}
This definition is captured by the following Haskell definitions:
\begin{code}
type Audience = (Assumptions, ArgWeight)
type Assumptions = [PropLiteral]
type ArgWeight = Argument -> Weight
type Weight = Double
\end{code}

Further, as each proposition is associated with a specific proof standard,
we need a mapping from propositions to proof standards:
\begin{code}
type PropStandard = PropLiteral -> PSName

data PSName = Scintilla 
  | Preponderance | ClearAndConvincing 
  | BeyondReasonableDoubt | DialecticalValidity
 deriving (Show, Eq)
\end{code}

\begin{spec}
psMap :: PSName -> ProofStandard 
\end{spec}

A proof standard is a function that given a proposition $p$, aggregates
arguments pro and con $p$ and decides whether it is acceptable or not:
\begin{code}
type ProofStandard = PropLiteral -> CAES -> Bool

newtype ProofStandardNamed = P (String, PropLiteral -> CAES -> Bool)
instance Eq ProofStandardNamed where
 P (l1, _) == P (l2, _) = l1 == l2
\end{code}
This aggregation process will be defined in detail in the next section,
but note that it is done relative to a specific CAES, and note the
cyclic dependence at the type level between |CAES| and |ProofStandard|.

The above definition of proof standard also demonstrates that
implementation in a typed language such as Haskell is a useful way of
verifying definitions from argumentation theoretic models. Our
implementation effort revealed that the original definition as given
in~\cite{Gordon09a} could not be realised as stated, because proof standards
in general not only depend on a set of arguments and the audience,
but may need the whole CAES.

\subsection{Evaluation}

Two concepts central to the evaluation of a CAES are
\emph{applicability of arguments}, which arguments should be
taken into account, and \emph{acceptability of propositions}, which
conclusions can be reached under the relevant proof standards, given
the beliefs of a specific audience.
\begin{definition}[Applicability of arguments]
Given a set of arguments and a set of assumptions (in an audience) in a CAES
$C$, then an argument $a = \langle P, E, c \rangle$ is
\emph{applicable} iff
\begin{itemize}
\item
    $p \in P$ implies $p$ is an assumption or [\,$\overline{p}$ is
    not an assumption and $p$ is acceptable in $C$\,] and
\item
    $e \in E$ implies $e$ is not an assumption and [\,$\overline{e}$
    is an assumption or $e$ is not acceptable in $C$\,].
\end{itemize}
\end{definition}
\begin{definition}[Acceptability of propositions]
Given a CAES $C$, a proposition $p$ is \emph{acceptable} in $C$ iff
$(s \; p \; C)$ is $true$, where $s$ is the proof standard for $p$.
\end{definition}

Note that these two definitions in general are mutually dependent
because acceptability depends on proof standards, and most sensible
proof standards depend on the applicability of arguments. This is the
reason that Carneades restricts the set of arguments to be acyclic. 
(Specific proof standards are considered in the next section.)
The realisation of applicability and acceptability in Haskell is
straightforward:
-- \begin{code}
-- applicable :: Argument -> CAES -> Bool
-- applicable (Arg (prems, excns, _)) caes@(CAES (_, (assumptions, _), _)) 
  -- = and  $  [(p `elem` assumptions)  ||     (p `acceptable` caes)  |  p <- prems  ]
            -- ++
            -- [(e `elem` assumptions)  `nor`  (e `acceptable` caes)  |  e <- excns  ]
      -- where
          -- x `nor` y = not (x || y)
-- acceptable :: PropLiteral -> CAES -> Bool
-- acceptable c caes@(CAES (_, _, standard))  
  -- = c `s` caes 
  -- where P (_, s) = standard c
-- \end{code}
\begin{code}
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

acceptable :: PropLiteral -> CAES -> Bool
acceptable c caes@(CAES (_, _, standard))  
  = c `s` caes 
  where s = psMap $ standard c
 

\end{code}


\subsection{Proof standards}

Carneades predefines five proof standards, originating from the work of
Freeman and Farley \cite{Freeman96,Farley95}: \emph{scintilla of
evidence}, \emph{preponderance of the evidence}, \emph{clear and convincing
evidence}, \emph{beyond reasonable doubt} and \emph{dialectical
validity}. Some proof standards depend on constants such as $\alpha$, 
$\beta$, $\gamma$; these are assumed to be defined once and globally.
This time, we proceed to give the definitions directly in Haskell,
as they really only are translitarations of the original definitions.

For a proposition $p$ to satisfy the weakest proof standard, scintilla of
evidence, there should be at least one applicable argument pro $p$ in the CAES:
\begin{code}
scintilla :: ProofStandard
scintilla p caes@(CAES (g, _, _))
 = any (`applicable` caes) (getArgs p g)
\end{code}

Preponderance of the evidence additionally requires the maximum weight of
the applicable arguments pro $p$ to be greater than the maximum weight of the
applicable arguments con $p$. The weight of zero arguments is taken to
be 0. As the maximal weight of applicable arguments pro and con is a recurring
theme in the definitions of several of the proof standards, we start by
defining those notions:


\begin{code}
maxWeightApplicable :: [Argument] -> CAES -> Weight
maxWeightApplicable as caes@(CAES (_, (_, argWeight), _))
 = foldl max 0 [argWeight a | a <- as, a `applicable` caes] 

maxWeightPro :: PropLiteral -> CAES -> Weight
maxWeightPro p caes@(CAES (g, _, _))
 = maxWeightApplicable (getArgs p g) caes

maxWeightCon :: PropLiteral -> CAES -> Weight
maxWeightCon p caes@(CAES (g, _, _))
 = maxWeightApplicable (getArgs (negate p) g) caes
\end{code}
%
We can then define the proof standard preponderance:
%
\begin{code}
preponderance :: ProofStandard 
preponderance p caes = maxWeightPro p caes > maxWeightCon p caes   
\end{code}


Clear and convincing evidence strengthen the preponderance constraints by
insisting that the difference between the maximal weights of the pro and con
arguments must be greater than a given positive constant $\beta$, and there
should furthermore be at least one applicable argument pro $p$ that is
stronger than a given positive constant $\alpha$:


\begin{code}
clear_and_convincing :: ProofStandard 
clear_and_convincing p caes
 =  (mwp > alpha) && (mwp - mwc > beta)
  where 
    mwp  =  maxWeightPro p caes
    mwc  =  maxWeightCon p caes
\end{code}

Beyond reasonable doubt has one further requirement: the maximal
strength of an argument con $p$ must be less than a given positive
constant $\gamma$; i.e., there must be no reasonable doubt:
\begin{code}
beyond_reasonable_doubt :: ProofStandard 
beyond_reasonable_doubt p caes
 = clear_and_convincing p caes && (maxWeightCon p caes < gamma)
\end{code}

Finally dialectical validity requires at least one applicable argument pro $p$
and no applicable arguments con $p$:
\begin{code}
dialectical_validity :: ProofStandard 
dialectical_validity p caes   
  = scintilla p caes && not (scintilla (negate p) caes)
\end{code}

%if False
Proof standard names can then be mapped to their according proof standard. 

\begin{code}
psMap :: PSName -> ProofStandard 
psMap Scintilla = scintilla
psMap Preponderance = preponderance
psMap ClearAndConvincing = clear_and_convincing
psMap BeyondReasonableDoubt = beyond_reasonable_doubt
psMap DialecticalValidity = dialectical_validity
\end{code}
%endif


\subsection{Convenience functions}
We provide a set of functions to facilitate construction of propositions,
arguments, argument sets and sets of assumptions. Together with the definitions
covered so far, this constitute our DSL for constructing Carneades
argumentation models.
\begin{spec}
mkProp         :: String -> PropLiteral                        
mkArg          :: [String] -> [String] -> String -> Argument   
mkArgSet       :: [Argument] -> ArgSet
mkAssumptions  :: [String] -> [PropLiteral]
\end{spec}
A string starting with a |'-'| is taken to denote a negative atomic
proposition.

To construct an audience, native Haskell tupling is used to combine
a set of assumptions and a weight function, exactly as it would be
done in the Carneades model:
\begin{spec}
audience :: Audience
audience = (assumptions, weight) 
\end{spec}
Carneades Argument Evaluation Structures and weight functions are defined in
a similar way, as will be shown in the next subsection.

Finally, we provide a function for retrieving the arguments for a
specific proposition from an argument set, a couple of functions to
retrieve all arguments and propositions respectively from an argument
set, and functions to retrieve the (not) applicable arguments or (not)
acceptable propositions from a CAES:
\begin{spec}
getArgs             :: PropLiteral  -> ArgSet  ->  [Argument]
getAllArgs          :: ArgSet                  ->  [Argument]
getProps            :: ArgSet                  ->  [PropLiteral]
applicableArgs      :: CAES                    ->  [Argument]
nonApplicableArgs   :: CAES                    ->  [Argument]
acceptableProps     :: CAES                    ->  [PropLiteral]
nonAcceptableProps  :: CAES                    ->  [PropLiteral]
\end{spec}

\begin{code}
getAllArgs :: ArgSet -> [Argument]
getAllArgs g = nub $ concatMap (snd . snd) (labNodes g)

getProps :: ArgSet -> [PropLiteral]
getProps g = map (fst . snd) (labNodes g)

applicableArgs :: CAES -> [Argument]
applicableArgs c@(CAES (argSet, _, _)) = filter (`applicable` c) (getAllArgs argSet)  

nonApplicableArgs :: CAES -> [Argument]
nonApplicableArgs c@(CAES (argSet, _, _)) = filter (not . (`applicable` c)) (getAllArgs argSet)

acceptableProps :: CAES  -> [PropLiteral]
acceptableProps c@(CAES (argSet, _, _)) = filter (`acceptable` c) (getProps argSet)

nonAcceptableProps :: CAES  -> [PropLiteral]
nonAcceptableProps c@(CAES (argSet, _, _)) = filter (not . (`acceptable` c)) (getProps argSet)
\end{code}


\begin{code}
contextP :: PropLiteral -> AGraph -> [Context (PropLiteral, [Argument]) ()]
contextP p = gsel (\ (_, _, a, _) -> fst a == p) 
     
getArgs :: PropLiteral -> AGraph -> [Argument]  
getArgs p g 
  =  case contextP p g of
       []                          -> []
       ((_, _, (_, args), _) : _)  -> args
\end{code}



\subsection{Graph construction}
We associate a graph along with a |Map| that stores the node number for every |PropLiteral| to make construction of the |AGraph| easier.

\begin{code}
type AGraph = ArgSet
type PropNode = LNode (PropLiteral, [Argument])
type AssociatedGraph = (AGraph, Map PropLiteral Node)
\end{code}

An argument graph is then constructed as following:
\begin{code}
mkArgSet :: [Argument] -> ArgSet
mkArgSet = mkArgGraph

mkArgGraph :: [Argument] -> AGraph
mkArgGraph = fst . foldr addArgument (empty, Map.empty)
\end{code}

Carneades uses the following definition for acyclicity:
\begin{definition}[Acyclic set of arguments]
\label{def:carneadesacyclic}
A list of arguments is acyclic iff its corresponding dependency graph is acyclic. The corresponding dependency graph has nodes for every literal appearing in the list of arguments. A node $p$ has a directed link to node $q$ whenever $p$ depends on $q$ in the sense that there is an argument pro or con $p$ that has $q$ or $\overline{q}$ in its list of premises or exceptions.
\end{definition}

So when we add an argument |(Arg premises exceptions conclusion)| to our graph, we need to add both the conclusion and its negate to the graph, adding edges for both to all premises and exceptions while adding the argument to the list of arguments for |conclusion| as well. 

\begin{code}
addArgument :: Argument -> AssociatedGraph -> AssociatedGraph
addArgument arg@(Arg (prem, exc, c)) gr  = 
  let  deps             =  prem ++ exc
       (gr',  nodeNr)   =  addArgument' arg gr
       (gr'', nodeNr')  =  addNode (negate c) gr'
  in addEdges nodeNr' deps $ addEdges nodeNr deps gr'' 
\end{code}


\begin{code}
addToContext :: Argument -> (Context (PropLiteral, [Argument]) (), AGraph) -> AGraph
addToContext arg ((adjb, n, (p, args), adja), g') = (adjb, n, (p, arg:args), adja) & g'

unsafeMatch :: Graph gr => Node -> gr a b -> (Context a b, gr a b)
unsafeMatch n g = mapFst fromJust $ match n g
\end{code}

Add an argument to the graph. If there is no node present yet for the conclusion insert it, in both cases add the argument to the context of the conclusion.
\begin{code}
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
\end{code}

Add a proposition to the graph.
\begin{code}
addNode :: PropLiteral -> AssociatedGraph -> (AssociatedGraph, Node)
addNode p gr@(g,m) 
 =  case Map.lookup p m of 
       Nothing -> ((insNode (nodeNr, (p, [])) g, Map.insert p nodeNr m), nodeNr)
       Just n  -> (gr, n)
    where nodeNr = Map.size m + 1
\end{code}

For a specific node, add an edge for every |PropLiteral| in the list for the given graph.
\begin{code}
addEdges :: Node -> [PropLiteral] -> AssociatedGraph -> AssociatedGraph
addEdges n ps (g, m) = addEdges' n (map (fromJust . flip Map.lookup m') ps)  (g', m')-- addEdges' c n ps (g', m')
 where  nodeNr    = Map.size m + 1 
        newProps  = filter ( (== Nothing) . flip Map.lookup m) ps  
        g'        = insNodes (propsToNodes newProps nodeNr) g
        m'        = Map.union m . Map.fromList $ zip newProps [nodeNr..]
\end{code}


Generate unlabelled edges from a |Node| to a list of |Node|s and add it to the graph.
\begin{code}
addEdges' :: Node -> [Node] -> AssociatedGraph -> AssociatedGraph
addEdges' c ps (g, m) = (insEdges edges' g, m)
 where  edges' = map (genEdge c) ps
        genEdge k l = (k, l, ())

\end{code}

Some useful functions.
\begin{code}
propsToNodes :: [PropLiteral] -> Node -> [PropNode]
propsToNodes ps n = zip [n..] (map (\ p -> (p, [])) ps)

checkCycle :: AGraph -> Bool
checkCycle = cyclic
-- Old definition using Graphalyze
-- not . null . cyclesIn

mkProp :: String -> PropLiteral
mkProp ('-':s)  = mapFst not (mkProp s)
mkProp s        = (True, s)

mkAssumptions :: [String] -> [PropLiteral]
mkAssumptions = map mkProp

mkArg :: [String] -> [String] -> String -> Argument
mkArg ps es c = Arg (map mkProp ps, map mkProp es, mkProp c)
\end{code}

Globally predefined alpha, beta and gamma. 
\begin{code}
alpha, beta, gamma :: Double
alpha  =  0.4
beta   =  0.3
gamma  =  0.2
\end{code}