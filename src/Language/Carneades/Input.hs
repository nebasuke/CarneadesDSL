-- | This is the input module accompanying the implementation of Carneades.
--  It defines a simple parser for a Carneades Argument Evaluation Structure
-- (CAES). 
--
-- Files are assumed to have the following order of content:
-- one argument or attack on each line, ending
-- in a dot. (Our parser is slightly more relaxed than this and 
-- doesn't care about whitespace.)
--
-- @att(a1,a2).@ or @arg(a1).@
--
-- Argument names are assumed to consist only of letters and numbers.
-- Arguments used in attacks should be declared separately as well. 
--
-- For a complete example see the included @examplecaes.txt@ file or
-- the accompanying ExampleCAES module.
module Language.Carneades.Input
  (
   -- * Parsing functions
   parseCAES, pCAES
   )
 where
import Language.Carneades.CarneadesDSL
import Text.Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellStyle)
import Data.Maybe(fromMaybe)

-- This allows the parsing of a CAES to have comments,
-- arguments consisting of a letter followed by alphanumerical characters, etc.
lexer :: P.TokenParser ()
lexer = P.makeTokenParser 
 (haskellStyle 
    { P.reservedNames = ["Scintilla", "Preponderance", "ClearAndConvincing",
                         "BeyondReasonableDoubt", "DialecticalValidity",
                         "scintilla", "preponderance", "clear_and_convincing",
                         "beyond_reasonable_doubt", "dialectical_validity"]
    }
 )

whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer

identifier :: Parser String
identifier = P.identifier lexer

stringLiteral :: Parser String
stringLiteral = P.stringLiteral lexer

symbol :: String -> Parser String
symbol = P.symbol lexer

float :: Parser Double
float = P.float lexer

-- A named Carneades argument.
data Argument' = Arg' String ([PropLiteral], [PropLiteral], PropLiteral)
 deriving (Eq, Show)

-- A weight to a name of a Carneades argument.
type Weight' = (String, Double)

-- A proof standard to a name of a Carneades argument.
type Standard' = (String, PSName)

-- |An argument name consists of a letter followed by one or more letters and digits,
-- underscore or \'. Alternatively, a string literal.
argName :: Parser String
argName = try identifier <|> stringLiteral

-- |Parses a proposition by parsing an identifier and using 'mkProp' from the 
-- CarneadesDSL package. 
pProposition :: Parser PropLiteral
pProposition = do 
                  p <- argName
                  whiteSpace
                  return (mkProp p)

-- |Parses a list of propositions. Propositions are separated by commas.
-- Optional whitespace is allowed in the list.
pPropositions :: Parser [PropLiteral]
pPropositions = do
                   _ <- char '[' >> whiteSpace
                   ps <- pProposition `sepBy` (symbol "," >> whiteSpace)
                   _ <- char ']' >> whiteSpace
                   return ps

-- |Parses a complete argument consists of @arg@ or @argument@ followed by an
 -- @argName@, two lists of propositions, and a conclusion. 
pArgument :: Parser Argument'
pArgument = do
               _ <- try (string "argument") <|> string "arg"
               whiteSpace
               name <- argName
               prems <- pPropositions
               excs <- pPropositions
               c <- pProposition
               return (Arg' name (prems, excs, c))

-- |Parses one declaration of a weight. A weight is declared by the string 
-- @weight@ followed by the name of a previously declared argument,
-- and a 'Double' assigned to that argument.
pWeight :: Parser Weight'
pWeight = do
             _ <- string "weight" >> whiteSpace
             name <- argName
             weight <- float
             return (name, weight)

-- |Parses a list of assumptions. A list of assumptions is just the keyword 
-- @assumptions@ followed by a list of propositions.
pAssumptions :: Parser Assumptions
pAssumptions = do
                  _ <- string "assumptions" >> whiteSpace
                  pPropositions

-- |Parses the name of a proof standard allowing both the names as given in 
-- the original paper and the constructors of PSName. 
pPSName :: Parser PSName
pPSName =  try ((try (string "Scintilla") <|> 
                      string "scintilla") 
                 >> return Scintilla) 
       <|> try ((try (string "Preponderance") <|> 
                      string "preponderance") 
                 >> return Preponderance) 
       <|> try ((try (string "ClearAndConvincing") <|> 
                      string "clear_and_convincing") 
                 >> return ClearAndConvincing) 
       <|> try ((try (string "BeyondReasonableDoubt") <|> 
                      string "beyond_reasonable_doubt") 
                 >> return BeyondReasonableDoubt) 
       <|> try ((try (string "DialecticalValidity") <|> 
                      string "dialectical_validity") 
                 >> return DialecticalValidity)
       
-- |Parses one declaration of a proof standard.  A proof standard is declared 
-- by the string @standard@ followed by a proposition and the name of a proof 
-- standard.
pStandard :: Parser Standard'
pStandard = do
                _ <- string "standard"
                whiteSpace
                name <- argName
                psName <- pPSName
                whiteSpace
                return (name, psName)

-- |Converts a named argument to the definition used in the implementation 
-- (and the paper).
argToArg :: Argument' -> Argument
argToArg (Arg' _ a) = Arg a

-- |Looks up a normal argument in a list of named argument and returns its name.
lookupArg :: Argument -> [Argument'] -> Maybe String
lookupArg _ [] = Nothing
lookupArg a (Arg' name a' : args)
 | a == Arg a' = Just name
 | otherwise = lookupArg a args

-- |Converts a list of named 'Argument\''s and named 'Weight\''s to a weight 
-- function. Arguments not assigned a weight will raise an error.
weightToWeight :: [Argument'] -> [Weight'] -> ArgWeight
weightToWeight args ws arg = 
 fromMaybe (error $ "no weight assigned to" ++ show arg)
          (lookupArg arg args >>= \name -> lookup name ws) 

-- |Converts a list of named 'Standard\''s to a standard function.
-- Propositions not assigned a weight will raise an error.
standardToStandard :: [Standard'] -> PropStandard
standardToStandard [] p = error $ "no standard assigned to" ++ show p
standardToStandard ((name, st) : sts) p 
 | mkProp name == p = st
 | otherwise        = standardToStandard sts p

-- |Parses the definition of a complete Carneades Argument Evaluation Structure
-- (CAES). 
-- 
-- A CAES is parsed in multiple stages: 
-- 
-- First parsing zero or more arguments: 
-- where a complete argument consists of @arg@ or @argument@ followed by an
-- @argName@ (a letter followed by one or more letters and digits,
-- underscore or \'; alternatively, a string literal), two lists of propositions,
-- and a conclusion. 
-- 
-- Then, zero or more weights, 
-- where a weight is declared by the string 
-- @weight@ followed by the name of a previously declared argument,
-- and a 'Double' assigned to that argument.
-- 
-- Then, a list of assumptions, 
-- where a list of assumptions is just the keyword 
-- @assumptions@ followed by a list of propositions.
--
-- Then a list of proof standard declarations,
-- where a proof standard is declared 
-- by the string @standard@ followed by a proposition and the name of a proof 
-- standard.
--
-- This is followed by an end of file token.
pCAES :: Parser CAES
pCAES = do 
           whiteSpace
           args <- many pArgument
           weights <- many pWeight
           assumps <- pAssumptions
           standards <- many pStandard
           eof
           let weight = weightToWeight args weights
           let audience = (assumps, weight) 
           let standard = standardToStandard standards
           let argSet = mkArgSet (map argToArg args)
           return (CAES (argSet, audience, standard))

-- |Parses a 'String' containing a CAES. 
-- If parsing fails, it propagates the parse error.
parseCAES :: String -> Either ParseError CAES
parseCAES = parse pCAES ""
