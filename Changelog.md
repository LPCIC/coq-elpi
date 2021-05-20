# Changelog

## Unreleased

Requires Elpi 1.13.5 and Coq 8.13.

### Derive
- New `lens` and `lens_laws` for regular and primitive records with or without
  parameters
- `derive` takes `#[only(this, that)]` to select the desired derivations
### API
- Fix `coq.elpi.accumulate` scope `current`, which was putting the closes in the
  current module for the current file, but was making them global for the files
  importing it
- New scope `library` for `coq.elpi.accumulate` which links the clauses to the
  library, that is the module named after the file.
- Fix databases are always available, no need to import files in the right order
  when databases have named clauses. The error "Error: unable to graft this
  clause: no clause named ..." should no more be raised in response to a
  `Require Import`.
- New `coq.strategy.*` to `set` and `get` the unfolding priority of constants
  followed by the term comparison algorithm Coq uses at type checking time.
- New `coq.env.record?` to test if an inductive is a record and if it has
  primitive projections
- New `coq.env.recursive?` to test if an inductive is recursive
- Change `coq.locate*` understands strings like `"lib:some.name"` which point
  to global references registered via the Coq `Register` command
- New `coq.ltac.fail` like `coq.error` but catch by Ltac
- New `@ltacfail!` to be used like `@ltacfail! Level => std.assert! ...` in
  tactic code to use `coq.ltac.fail` instead of `coq.error` in case of failure
- Change failure as is `elpi fails` (no more clauses to try) or
  `elpi run out of steps` are not considered Ltac failures anymore, but rather
  fatal errors. Add a clause `solve _ _ :- coq.ltac.fail _` to preserve the
  old behavior.
- New `coq.ltac.collect-goals` to turn unresolved unification variables into
  goals.
- Fix `coq.env.add-const` now accepts an opaque definition with no given type.
  The body is assumed to be well typed and is quickly retypechecked.

### HOAS
- Fix handling of default case in `match`, now Coq's `if _ then _ else _`
  works just fine.
- New quotation `{{:gref id }}` and `{{:gref lib:qualid }}` that unfolds to the
  `gref` data type (`{{ id }}` and `{{ lib:qualid }}` unfold to terms)
- Change `solve` only takes 2 arguments (the arguments passed at tactic
  invocation time are now part of the goal) and the first argument is a single
  goal, not a list thereof. The second argument is now a `sealed-goal`.
- Change `refine` now generates a list of `sealed-goal`s
- Change `goal` now carries two unification variables standing for the
  raw solution to goal and the elaborated, well typed, one. Assigning a term
  to the raw variable triggers a call to `coq.elaborate-skeleton` which in turn
  assigns the other one to the (partial) proof term.
  Assigning the elaborated variable directly does not trigger a type check
  of the term.

### Vernacular
- New `attributes` tactic argument (for `Tactic Notation`)
- New `elpi tac` can receive attributes via the usual `#[stuff] tac` syntax
- New syntax to pass Elpi tactics arguments coming from Ltac variables:
  - `ltac_string:(v)` (for `v` of type `string` or `ident`)
  - `ltac_int:(v)` (for `v` of type `int`)
  - `ltac_term_list:(v)` (for `v` of type `constr` or `open_constr`)
  - `ltac_attributes:(v)` (for `v` of type `attributes`)
  Example:
  ```coq
  Tactic Notation "foo" string(X) ident(Y) int(Z) constr(T) constr_list(L) :=
    elpi foo ltac_string:(X) ltac_string:(T) ltac_int:(Z) (T) ltac_term_list(L).
  ```
  lets one write `foo "a" b 3 nat t1 t2 t3` in any Ltac context. For attributes
  one has to place `ltac_attributes:(v)` in front of `elpi`, as in:
  ```coq
  Tactic Notation "foo" "#[" attributes(A) "]" :=
    ltac_attributes:(A) elpi foo.
  ```
  The usual prefix notation is also possible with the following limitations
  due to a parsing conflicts in the Coq grammar (at the time of writing):
  ```coq
  Tactic Notation "#[" attributes(A) "]" "tac" :=
    ltac_attributes:(A) elpi tac.
  ``` 
  - `#[ att ] tac.` does not parse
  - `(#[ att ] tac).` works
  - `idtac; #[ att ] tac.` works

## [1.9.7] - 15-04-2021

Requires Elpi 1.13.1 and Coq 8.13.

### Vernacular
- New attribute `#[skip="rex"]` and `#[only="rex"]` for the
  `Elpi Acumulate` family of commands which let one accumulate
  a piece of (compatibility) code only on some Coq versions.

## [1.9.6] - 13-04-2021

Requires Elpi 1.13.1 and Coq 8.13.

### API
- New `coq.reduction.lazy.norm`
- New `coq.reduction.native.norm`
- New `coq.reduction.native.available?`
- Rename `coq.reduction.cbv.whd_all` -> `coq.reduction.cbv.norm`
- Rename `coq.reduction.vm.whd_all` -> `coq.reduction.vm.norm`

## [1.9.5] - 26-03-2021

Requires Elpi 1.13 and Coq 8.13.

### Vernacular
- Commands, Tactics and Db cannot be declared inside sections or modules
  (it never really worked, but now you get an error message).
- Clauses which are accumulated via `coq.elpi.accumulate` and are not `@local!`
  survive section closing if they don't mention the section variables being
  discharged.

### Typechecker
- Warnings can be turned into errors by passing Coq `-w +elpi.typecheck`.

### API
- New `coq.CS.db-for` to filter the CS db given a projection or a canonical
  value, or both.
- New `coq.warning` like `coq.warn` but with a category and name, so that
  the message can be silenced or turned into an error.

## [1.9.4] - 17-03-2021

Requires Elpi 1.13 and Coq 8.13.

### Elpi
- Calls to APIs that only read the global state are much faster (thousands of
  times faster)
- Fix compilation with OCaml 4.12

### API
- Fix issue with `coq.env.add-abbreviation` when given a term with binders
  having overlapping `name`s.
- New `copy-indt-decl` 
- New `coq.coercion.declare` is able to infer the endpoints if omitted

## [1.9.3] - 18-02-2021

Requires Elpi 1.13 and Coq 8.13.

### Elpi
- Fix issue with async-mode (Elpi commands can change the parser)

### API
- New `attmap` attribute type to represent associative maps over strings, eg
  `#[foo(x = "a", y = "b")]`

## [1.9.2] - 12-02-2021

Requires Elpi 1.13 and Coq 8.13.

### API
- Fix `elpi.loc` computation when run in interactive mode.
- New `@using! S` attribute for `coq.env.add-const` akin to Coq's `#[using=S]`.

## [1.9.1] - 11-02-2021

Requires Elpi 1.13 and Coq 8.13.

### API
- Fix `coq.env.add-section-variable` and `coq.env.add-axiom` were not handling
  universes correctly.

### Build system

- New target `build` which only builds elpi and the apps
- New target `test` which runs all tests for elpi and the apps
- OPAM package only calls `test` only if requested, hence the package typically
  installs faster

## [1.9.0] - 10-02-2021

Requires Elpi 1.13 and Coq 8.13.

### HOAS
- Fix `coq.env.indt-decl` to generate a `record-decl` for records.

### Elpi
- Fix issue with the compiler cache when used in async-mode (via CoqIDE or
  vscoq).

### API
- New type `coq.pp` and `coq.pp.box` to describe Coq's pretty printer box model
- New `coq.pp->string` to turn formatting boxes into a string
- New `coq.term->pp` to turn formatting boxes into a string
- New `@ppall!` attribute to print terms in full details
- New `@ppmost!` attribute to print terms in a reparsable way
- New `@ppwidth! N` attribute to specify the maximal line length when turning
  formatting boxes into strings
- New `fold-map` to map a term with an accumulator
- New `coq.env.add-section-variable`
- New `coq.env.add-axiom`
- Deprecate `coq.env.add-const` for declaring axioms or section variables. The
  deprecation warning is called `elpi.add-const-for-axiom-or-sectionvar` and
  can be turned into an error by passing to `coqc` the option
  `-w +elpi.add-const-for-axiom-or-sectionvar`

### Tooling
- The `COQ_ELPI_ATTRIBUTES=text` parses `text` as Coq attributes `#[elpi(text)]`
  and passes them to all commands. Attributes in the `elpi.` namespace are
  silently ignored by commands not using them.
- Attribute `elpi.loc` carries the `loc` of the command being run (if exported
  with `Elpi Export cmd`). This location does not comprise control flags
  (eg `Fail`, `Time`) nor attributes. This limitation will be lifted in
  Coq 8.14 (8.13 does not expose this parsing information to plugins).

## [1.8.1] - 11-12-2020

Requires Elpi 1.12 and Coq 8.13.
### HOAS
- Illformed terms like `global (const X)` (which have no
  representation in Coq) are now reported with a proper error message.
  Whe passed to `coq.term->string`, instead of a fatal error, we pick for
  the illformed sub term the `unknown_gref` special constant.

## [1.8.0] - 29-11-2020

Requires Elpi 1.12 and Coq 8.12.

### API
- New `@primitive!` attribute for `coq.env.add-indt` allowing one to declare
  primitive records. So far no term syntax for primitive projects is supported,
  their "non primitive" version is always used instead.

### HOAS
- Best effort support for Coq's `let (x, y, .. ) := t in ` in quotations.

### API
- Fix `coq.term->gref` skips over casts
## [1.7.0] - 26-11-2020

Requires Elpi 1.12 and Coq 8.12.

### HOAS
- New `primitive (uint63 <i>)` term constructor
- New `primitive (float64 <f>)` term constructor

### API
- New `coq.reduction.lazy.whd_all`
- New `coq.reduction.cbv.whd_all`
- New `coq.reduction.vm.whd_all`
- New `coq.env.const-primitive?`
- Fix argument `const-decl` is accepted even if the name is "_", allowing one
  to write `Elpi command Definition _ : type := body`
- Fix `coq.notation.abbreviation` gives an error if too few arguments are
  provided

### Sources
  Major reorganization of sources:
  - src/ is for .ml files
  - elpi/ for .elpi files
  - theories/ for .v files meant to be installed
  - tests/ for the test suite, not to be installed
  - examples/ for tests (not to be installed)

  Moreover the apps/ directory is for applications written in Coq-Elpi, their
  structure follows the same convention

### NES (Namespace Emulation System)
  - POC application emulating name spaces on top of modules

### Elpi integration
  - Use Elpi 1.12 API to implement a compiler cache and avoid recompiling
    over and over the same programs.

## [1.6.0] - 21-08-2020

Requires Elpi 1.11 and Coq 8.12.

### UIs
- Display failures generated by `std.assert!` as errors

### Derive
- Use the new `coq.elaborate-skeleton` API to insert coercions

### Fix
- Embedding for sorts was incorrectly mapping `Prop` to `sprop`
- `coq.env.add-const` made 8.12 friendly with a workaround for coq/coq#12759

### API
- New `coq.elaborate-skeleton` and `coq.elaborate-ty-skeleton` that run
  Coq's elaborator on a term obtained by disregarding evars and universes
  in the given input. Unfortunately Coq's elaborator does not take terms
  as input, but glob terms, and the conversion function is not lossless.
  See also `lib:elpi.hole`.
- New `coq.elaborate-indt-decl-skeleton` to elaborate an inductive type
  declaration.
- New `coq.elaborate-arity-skeleton` to elaborate an arity.
- New `coq.env.current-path` to get the current module path.
- New `coq.modpath->path` and `coq.modpath->path` to get access to the
  components of a module path.
- Change `coq.elpi.accumulate` understands the `@local!` attribute, which makes
  the clauses `Local` to the module into which they live.

### HOAS
- New `lib:elpi.hole` constant that can be used in place of a unification
  variable to denote an implicit argument when calling `coq.*-skeleton` APIs

## [1.5.1] - 29-07-2020

Requires Elpi 1.11 and Coq 8.12.

### API:
  Locality is now supported by `coq.CS.declare-instance`

## [1.5.0] - 29-07-2020

Requires Elpi 1.11 and Coq 8.11.

### HOAS
- New option `@holes!` to be assumed (as in `@holes! => ...`) before
  calling any Coq API. When this option is given unknown unification variables
  are interpreted as "implicit arguments" (linear holes that see all the
  variables in scope). If the unification variable is outside the pattern
  fragment the following heuristic is applied: arguments that are not variables
  are heuristically dropped; arguments which are variables but occur multiple
  times are kept only once (the first occurrence is kept, the others are
  dropped).

### API
- New `coq.arguments.set-default-implicit` that behaves like
  `Arguments foo : default implicits`
- Change of arguments of type `@global?` attributes `@local!` or `@global!`.
  In order to pass a locality directive one has to do something like
    `@global! => coq.add-something`
  Locality is understood by:
  - `coq.TC.declare-instance`
  - `coq.coercion.declare`
  - `coq.arguments.set-implicit`
  - `coq.arguments.set-default-implicit`
  - `coq.arguments.set-name`
  - `coq.arguments.set-scope`
  - `coq.arguments.set-simplification`
  - `coq.notation.add-abbreviation`
  - `coq.env.add-const`
- Change of argument for deprecation to attribute `@deprecated! Since Message`.
  In order to pass a deprecation directive one has to do something like
    `@deprecated! "8.11.0" "use this instead" => coq.add-something`
  Deprecation is understood by:
  - `coq.notation.add-abbreviation`
- New macro `@transparent!` with value `ff` to be used with `coq.env.add-const`

### Elaborator
- `engine/elaborator.elpi` is now installed (but not used by default).
  One can `Elpi Accumulate "engine/elaborator.elpi".` in order to load it.
  It is too experimental to use it in production, but it is also hard to
  experiment with it without having it installed.

### CI
- Switch to Github Actions and Coq Community's Docker workflow

### Bugfix
- anonymous record fields are not given a generated name anymore
- `coq.typecheck` and `coq.typecheck-ty` API now ensure that all unification
  problems required by type checking are actually solved by Coq's unifier
- some debug printings used to raise errors in corner cases, now fixed

## [1.4.1] - 2020-06-10

Minor fixes

- Missing opaque data type declaration for `abbreviation` (could lead to
  confusing type errors)
- Parse also "keywords" where `qualified_name` is expected. `Elpi Export x.`
  turns `x` into a keyword, and that used to break commands
  `Elpi Something x ...`. Parsing of all commands is now resilient to this.

## [1.4.0] - 2020-05-19

Requires Elpi 1.11 and Coq 8.11 or 8.12.

The main visible change is the `indt-decl` data type that now faithfully
represents an inductive type declaration (including the implicit status of
parameters). Also all the predicates implemented in `coq-lib` are now in
the `coq.` namespace.

### API
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
- Change `arity->sort` -> `coq.arity->sort`
- Change `term->gref` -> `coq.term->gref`
- Change `fresh-type` -> `coq.fresh-type`
- Change `build-match` -> `coq.build-match`
- Change `map-under-fun` -> `coq.map-under-fun`
- Change `iter-under-fun` -> `coq.iter-under-fun`
- Change `bind-ind-arity` -> `coq.bind-ind-arity`
- Change `with-TC` -> `coq.with-TC`
- Change `valid-attribute` -> `coq.valid-attribute`
- Change `is-one-of` -> `coq.is-one-of`
- Change `parse-attributes` -> `coq.parse-attributes`
- Change `mk-app` -> `coq.mk-app`
- Change `mk-app-uvar` -> `coq.mk-app-uvar`
- Change `mk-eta` -> `coq.mk-eta`

### Universes
- New support for `Type@{name}` in Coq `{{ quotations }}`.
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
    parameters, and the inductive type arity (see below) is no more a simple term
    but rather an `arity` (all its parameters are non uniform)
  - the `constructor` constructor now carries an `arity` so that non uniform
    parameters can be represented faitfully
- New `arity` data type, constructors are `parameter` (shared with `indt-decl`)
  and `arity`.
- New `indt-decl` argument type introduced in version 1.3 now supports the
  syntax of inductive types (not just records). Eg
  `Elpi command Inductive P {A} t : I := | K1 .. | K2 ..`.
- Change `context-item` now carries an `id` and an `implicit-kind`
- Change `const-decl` now carries an arity to describe the parameters of
  the definition in a faithful way
- New `@pi-parameter ID Ty p\ ...` to postulate a nominal `p` with type `Ty`
  and a name built out of the id `ID`

### Derive

- New derivations `derive.invert` and `derive.idx2inv` now called by `derive`
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
- Failure of `coq.ltac.call` is now turned into logical failure, as any
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
