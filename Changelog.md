# Changelog

## [1.1.0] - 2019-10-10

### derive.param2

- interface made consistent with other derivations: `derive.param2` takes in
  input optional suffix, instead of the full name of the derived concept

- storage of previous derivations based on Elpi Db

- the derivation generates nicer types for relators over fixpoints (the new
  types are convertible to the old ones, but the fixpoint is not expanded).
  PR #84 by Cyril Cohen

### Documentation

- Improved documentation of `coq.typecheck`

## [1.0.0] - 2019-10-09

- First public release