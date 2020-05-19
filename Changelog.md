# Changelog

## UNRELEASED

Requires Elpi 1.11.x and Coq 8.11.x or 8.12.x

### APIs:
- New `coq.notation.abbreviation-body` to retrieve the number of arguments and
  body of a syntactic definition.
- New `coq.id->name` to convert a relevant id into an irrelevant pretty printing
  hint.
- New `coq.mk-n-holes ` to produce a list of flexible terms.
- New `coq.env.indt-decl` to read for the environment an inductive type
  represented in HOAS form
- `coq.env.indt->decl` renamed `coq.build-indt-decl`
- New `coq.env.rename-indt-decl`
- Change `coq.env.add-indt` now sets the imlicit status of the inductive
  type and its constructors (since the `parameter` constructor can carry it)
- New `coq.arity->nparams` to count the number of parameters
- Change `parse-attributes` made deterministic
- Change `coq.unify-leq` and `coq.unify-eq` now return a diagnostic
- Change `subst-prod` -> `coq.subst-prod`
- Change `subst-fun` -> `coq.subst-fun`
- Change `prod->fun` -> `coq.prod->fun`
- Change `count-prods` -> `coq.count-prods`
- Change `prod-R-fun` -> `coq.prod-R-fun`
- Change `safe-dest-app` -> `coq.safe-dest-app`

### Universes:
- New support for `Type@{name}` in Coq {{ quotations }}.
- Fix more precise promotion of universe variables to universe global names
  in builtins changing the Coq environment (eg `coq.env.add-const`).
- New user error when `coq.elpi.accumulate` is given a clause that mentions
  universe variables: only global universes can be stored in a DB.

### HOAS

- Change `indt-decl`:
  - the `parameter` constructor carries an `id`, `imlpicit_kind` and a type
  - the `coinductive` constructor was removed, the `inductive` one carries
    a `bool`, `tt` for inductive, `ff` for coinductive
  - the `inductive` constructor no more carries the number of non uniform
    parameters has gone, and the inductive type arity is no more a simple term
    but rather an `arity` (all its parameters are non uniform)
  - the `constructor` constructor now carries an `arity` so that non uniform
    parameters can be represented faitfully
- New `arity` data type, constructors are `parameter` (shared with `indt-decl`)
  and `arity`.
- New `indt-decl` argument type introduced in version 1.3 now supports the
  syntax of inductive types (not just records). Eg
  `Elpi command Inductive P {A} t : I := | K1 .. | K2 ..`.
- Change `context-item` now carries an `id` and an implicit status
- Change `const-decl` now carries an arity to describe the parameters of
  the definition in a faithful way
- New `@pi-parameter ID Ty p\ ...` to postulate a nominal `p` with type `Ty`
  and a name out of id `ID`

### Derive

- New derivations `derive.invert` and `derive.idx2inv`
- New global command `derive` taking in input the name of an inductive
  or an inductive declaration. In the latter case all derivations are placed
  in a module named after the inductive

## [1.3.1] - 2020-03-01

Port to Coq 8.11, two API changes:
- `field` constructor of `indt-decl` takes an argument of type
  `field-attributes` rather than a simple `bool`. The macro `@coercion!` works
  in both versions, as well as omitting the attribute using `_`. In 8.11 it is
  possible to disable canonical inference for a field using the
  `(canonical false)` attribute.
- `coq.env.add-abbreviation` takes an extra argument (deprecation info). Code
  working on both versions can be obtained as follows:
  ```prolog
  if (coq.version _ 8 10 _)
    (std.unsafe-cast coq.notation.add-abbreviation F, F ... Abbrev)
    (std.unsafe-cast coq.notation.add-abbreviation G, G ... Deprecation Abbrev).
  ```

## [1.3.0] - 2020-02-27

Requires Elpi 1.10 and Coq 8.10 or 8.11.

The main visible change is that opaque data types such as `@constructor`,
`@inductive` and `@constant` are now written without the `@`, since Elpi now
supports the `typeabbrev` directive.

The main invisible change is that code accumulated into commands and tactics is
"compiled" by Elpi once and forall in the context in which it is accumulated. As
a consequence Coq code inside `{{quotations}}` is processed in that, and only
that, context of notations, scopes, etc. Data bases are compiled every time it
is needed in the current Coq context, hence quotations should be used with care.

The file `coq-HOAS.elpi` is now distributed as part of `coq-builtin.elpi`.

### Vernacular

- New `Elpi Export command` to make `command` available without the `Elpi`
  prefix.
- `Elpi command` (exported or not) can now access Coq's attributes (the
  `#[option]` thing). See the HOAS section below.
- Coq keywords or symbols passed to command and tactics are interpreted as
  strings even if not quoted. Eg `Elpi command =>` is the same of
  `Elpi command "=>"`.
- The identifiers `Record`, `Definition`, `Axioms` and `Context` are now
  reserved (see the HOAS section below). In order to pass them (as strings)
  one has to quote them.

### APIs

- New `coq.typecheck-ty` to typecheck a type (outputs a universe)
- New `coq.env.import/export-module`.
- New `coq.env.begin/end-section`.
- New `coq.notation.abbreviation` to unfold an abbreviation.
- New `coq.locate-abbreviation` to locate abbreviations.
- New `coq.locate-any` that never fails and gives a list of possible
  interpretations (term, abbreviation, module, module type).
- Rename `coq.env.typeof-gr` to `coq.env.typeof`.
- Rename `term->gr` to `germ->gref`.
- Rename `coq.gr->*` to `coq.gref->*string*`
- Change `coq.typecheck` and `coq.typecheck-indt-decl` so that they
  never fail and have a 3rd argument of type `diagnostic` (from Elpi 1.9)
  to signal success or errors (that can be printed).
- Change `coq.elpi.accumulate` so that one can put the clause either in
  current module from which the program is started, or in the current
  module while the program runs (which can be different if one uses the
  `coq.env.begin-module` API).
- Remove `coq.elaborate` and `coq.elaborate-indt-decl`.
- Fix `coq.typecheck T TY` to uses Coq's unification to equate
  the type inferred for `T` and `TY` (when it is provided by
  the user).
- Fix `coq.CS.*` w.r.t. default instances of canonical structures.
- Fix all APIs changing the Coq global state to abort if they are used
  from a tactic.
- Fix `coq.gr->string` to not duplicate the label part of the name

### HOAS

- Change context entry `def` to not carry a cache for the normal form
  of the defined term (now cached by a specific `cache` context entry).
  `def` now carries the exact same information of a `let`, as `decl`
  carries the same information of a `fun`.
- New `indt-decl` argument type with a concrete syntax that mimics the
  standard one for records. Eg `Elpi command Record x := K { f : T }`.
- New `const-decl` argument type with a concrete syntax that mimics the
  standard one for definitions or axioms.
  Eg `Elpi command Definition x := t.`.
- New `ctx-decl` argument type with a concrete syntax that mimics the
  standard one for contexts. Eg `Elpi command Context T (x : T).`.
- Add to the context under which `main` is run the list of attributes
  passed to the command invocation (Coq syntax is for example `#[myflag]`).
  See the `attribute-value` data type in `coq-builtin.elpi` and
  `parse-attributes` helper in `coq-lib.elpi`.

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
