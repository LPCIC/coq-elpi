# Changelog

## [1.2.0] - 2019-10-30

### APIs

- New `coq.gr->path` to get the path components as a list of strings
- Failure of `coq.ltac1.call` is now turned into logical failure, as any
  other Elpi tactic
- Fix `coq.end.add-indt` in the case of record (was not flagging the inductive
  as such)
- Fix `coq.version`, wrong parsing of beta versions 
- Expose `set` and `map` from Elpi 1.8 (generic data structure for ground terms)

### Documentation

- Improve reflexive tactic demo
- Fix documentation of `coq.gr->*` APIs
- `coq-HOAS.elpi`, `coq-lib.elpi` and `coq-builtin.elpi` are now installed since
  they provide useful doc (but are not needed by the runtime, since they are
  embedded in `elpi.vo`)

## [1.1.0] - 2019-10-10

### derive.param2

- interface made consistent with other derivations: `derive.param2` takes in
  input optional suffix, instead of the full name of the derived concept

- storage of previous derivations based on Elpi Db

- the derivation generates nicer types for relators over fixpoints (the new
  types are convertible to the old ones, but the fixpoint is not expanded).
  PR [#84](https://github.com/LPCIC/coq-elpi/pull/84/) by Cyril Cohen

### Documentation

- Improved documentation of `coq.typecheck`

## [1.0.0] - 2019-10-09

- First public release
