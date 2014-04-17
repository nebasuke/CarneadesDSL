-- | This is the input module accompanying the implementation of Carneades.
--  It defines a simple parser for a Carneades Argument Evaluation Structure
-- (CAES). 
--
-- Files are assumed to have the following order of content:
-- one argument or attack on each line, ending
-- in a dot. (Our parser is slightly more relaxed than this and doesn't care about whitespace.)
--
-- @att(a1,a2).@ or @arg(a1).@
--
-- Argument names are assumed to consist only of letters and numbers.
-- Arguments used in attacks should be declared separately as well. 
module Language.Carneades.Input
  (
   -- * Parsing functions
   parseCAES, pCAES
   )
 where
import Language.Carneades.CarneadesDSL
import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Char (char, string)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language(haskellStyle)
import Text.Parsec.Error(errorMessages, messageString)
import Data.Either (partitionEithers)

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

brackets :: Parser a -> Parser a
brackets = P.brackets lexer

stringLiteral :: Parser String
stringLiteral = P.stringLiteral lexer

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
-- underscore or \'. 
argName :: Parser String
argName = identifier 

-- |Parses a proposition by parsing an identifier and using 'mkProp' from the 
-- CarneadesDSL package. 
pProposition :: Parser PropLiteral
pProposition = do 
                  p <- try identifier <|> stringLiteral
                  whiteSpace
                  return (mkProp p)


pPropositions :: Parser [PropLiteral]
pPropositions = do 
                   char '[' >> whiteSpace
                   ps <- pProposition `sepBy` (symbol ",")
                   char ']' >> whiteSpace
                   return ps

-- |A complete argument consists of @arg(argName).@
pArgument :: Parser Argument'
pArgument = do 
               try (string "argument") <|> string "arg"
               whiteSpace
               name <- argName
               prems <- pPropositions
               excs <- pPropositions
               c <- pProposition
               return (Arg' name (prems, excs, c))


pWeight :: Parser Weight'
pWeight = do
             string "weight" >> whiteSpace
             name <- argName
             weight <- float
             return (name, weight)
             
pAssumptions :: Parser Assumptions
pAssumptions = do 
                  string "assumptions" >> whiteSpace
                  pPropositions

pPSName :: Parser PSName
pPSName =  try (do (try (string "Scintilla") <|> 
                         string "Scintilla") 
                    >> return Scintilla) 
       <|> try (do (try (string "Scintilla") <|> 
                         string "Scintilla") 
                    >> return Scintilla) 
            
pStandard :: Parser Standard'
pStandard = do 
                string "weight"
                name <- argName
                psName <- pPSName
                return (name, psName)

arg'ToArg :: Argument' -> Argument
arg'ToArg (Arg' _ a) = Arg a

lookupArg :: Argument -> [Argument'] -> Maybe String
lookupArg a [] = Nothing 
lookupArg a ((Arg' name a') : args) 
 | a == (Arg a') = Just name
 | otherwise = lookupArg a args


weight'ToWeight :: [Argument'] -> [Weight'] -> ArgWeight
weight'ToWeight args ws arg = 
 case (lookupArg arg args >>= \name -> lookup name ws) of
   Nothing -> error $ "no weight assigned to" ++ show arg
   Just w  -> undefined
    
standard'ToStandard :: [Standard'] -> PropStandard
standard'ToStandard [] p = error $ "no standard assigned to" ++ show p
standard'ToStandard ((name, st) : sts) p 
 | mkProp name == p = st
 | otherwise        = standard'ToStandard sts p

pCAES :: Parser CAES
pCAES = do 
           whiteSpace
           args <- many pArgument
           weights <- many pWeight
           assumps <- pAssumptions
           standards <- many pStandard
           let weight = weight'ToWeight args weights
           let audience = (assumps, weight) 
           let standard = standard'ToStandard standards
           let argSet = mkArgSet (map arg'ToArg args)
           return (CAES (argSet, audience, standard))

-- |Parses a 'String' containing a CAES. 
-- If parsing fails, it propagates the parse error.
parseCAES :: String -> Either ParseError CAES
parseCAES input = parse pCAES "" input