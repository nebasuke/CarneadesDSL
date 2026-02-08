# CarneadesDSL

An implementation and domain-specific language for the
[Carneades argumentation model](https://carneades.github.io/).

## Synopsis

CarneadesDSL provides a Haskell DSL for constructing and evaluating
Carneades Argument Evaluation Structures (CAES). It supports five
predefined proof standards and includes a parser for external CAES
definitions.

## Usage

```haskell
import Language.Carneades.CarneadesDSL
import Language.Carneades.ExampleCAES (caes, argSet)

-- Construct propositions and arguments
let p = mkProp "intent"
let a = mkArg ["witness"] ["unreliable"] "intent"

-- Query a CAES
acceptable (mkProp "murder") caes   -- False
applicableArgs caes                 -- [applicable arguments]
```

## Parsing

CAES definitions can be parsed from text files:

```haskell
import Language.Carneades.Input (parseCAES)

main :: IO ()
main = do
  input <- readFile "examplecaes.txt"
  case parseCAES input of
    Left err   -> print err
    Right caes -> print (acceptableProps caes)
```

## References

See "Haskell Gets Argumentative" in the Proceedings of Symposium on
Trends in Functional Programming (TFP 2012) by Bas van Gijzel and
Henrik Nilsson.

For the papers accompanying this library see
[Google Scholar](https://scholar.google.com/citations?user=Xu4yjvwAAAAJ&hl).

## License

BSD-3-Clause (see [LICENSE](LICENSE))
