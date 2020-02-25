# Changelog

## [1.3.0] - UNRELEASED

Switch to Elpi 1.9. The main visible change is that opaque data
types such as `@constructor`, `@inductive` and `@constant` are now
written without the `@`.

### Vernacular

- New `Elpi Export command` to make `command` available without the `Elpi`
  prefix.

### APIs

- New `coq.typecheck-ty` to typecheck a type (outputs a universe)
- New `coq.env.import/export-module`.
- New `coq.env.begin/end-section`.
- Rename `coq.env.typeof-gr` to `coq.env.typeof`.
- Change `coq.typecheck` and `coq.typecheck-indt-decl` so that they
  never fail and have a 3rd argument of type `diagnostic` (from Elpi 1.9)
  to signal success or errors (that can be printed).
- Remove `coq.elaborate` and `coq.elaborate-indt-decl`.
- Fix `coq.typecheck T TY` to uses Coq's unification to equate
  the type inferred for `T` and `TY` (when it is provided by
  the user).
- Fix `coq.CS.*` w.r.t. default instances of canonical structures.
- Fix all APIs changing the Coq global state to abort if they are used
  from a tactic.
- Fix `coq.gr->string` to not duplicate the label part of the name
- Rename `coq.gr->*` to `coq.gref->*string*`

### HOAS

- Add to the context under which `main` is run the list of attributes
  passed to the command invocation (Coq syntax is for example `#[myflag]`).
  See the attribute-value data type in `coq-builtin.elpi`.
- Change context entry `def` to not carry a cache for the normal form
  of the defined term (now cached by a specific `cache` context entry).
  `def` now carries the exact same information of a `let`, as `decl`
  carries the same information of a `fun`.
- New `indt-decl` argument type with a concrete syntax that mimicks the
  standard one for records. Eg `Elpi command ... Record x := K { f : T }`.

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
