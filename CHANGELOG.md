# Changelog

## 2.0.0.0

* Modernise build: require `cabal-version: 3.0`, GHC 9.4+
* Move sources under `src/` layout
* Convert literate Haskell (`.lhs`) to plain Haskell (`.hs`); originals
  preserved in `doc/`
* Add `-Wall`-clean compilation
* Add test suite (tasty + HUnit)
* Add GitHub Actions CI (GHC 9.4 / 9.6 / 9.8 / 9.10)
* Remove `Setup.hs`
* Update maintainer email, copyright years, and homepage URL

## 1.3

* An Input module, allowing files to be parsed.
* An example of the usage of this module.

## 1.2

* This package version is now compatible with the translation package
  CarneadesIntoDung.
* Change the use of proof standards to rely on the definition of `PSName`
  to allow for an easier translation.
* Fix the definition of applicability to include all three conditions.

## 1.1.0.1

* Initial Hackage release.
