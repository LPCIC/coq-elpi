# UNRELEASED

### APPS:
- derive: support for primitive strings in `param1` and `param1_trivial`
- derive: support for `is_true` in `param1_trivial` (based on pre-existing
  special support for `is_eq` and `is_bool`)

### API
- New `coq.univ.alg-super` that relates a univ `U` to its algebraic successor
  `V`, that is `U+1` and not any `V` s.t. `U < V`
- New `coq.register` API

### HOAS
- New `@keep-alg-univs!` option for all APIs taking terms. By default algebraic
  universes are replaced by named universes. See the `coq.univ.alg-super` API.

# [2.5.0] 18/2/2025

Requires Elpi 2.0.7 and Coq 8.20 or Rocq 9.0.

### Packaging
- rename to `rocq-elpi` (`coq-elpi` is a transitional package)
- remove cram tests
- separate tests bsed on `rocq-stdlib`, the main build targets
  just depend on `rocq-core`
- CI based on docker images rather than ocaml setup

### APPS
- derive: fix missing universe constraints in `param2`
- derive: new `param2.register` command
- derive: improve generated names in `param2`
- derive: put eqb AST into a dedicated namespace
- derive: new (experimental) derive.eqbOK.register_axiom
- eltac: apply and rewrite examples

### API
- `coq.count-prods` now count products modulo reduction,
  rather than purely syntactically
- `coq.arity->sort` now attempts reduction to find a sort or prod,
  before failing
- `coq.arity->sort` now handles let-in

# [2.4.0] 15/1/2025

Requires Elpi 2.0.7 and Coq 8.20.

### API
- Change `coq.env.add-section-variable` now takes the implicit status of the
  variable

# [2.3.0] - 6/12/2024

Requires Elpi 2.0.3 and Coq 8.20.

The major change is the port to Elpi 2.0 that reports type checking errors
to the location of the offending term and not its enclosing rule.

### Vernacular
- `Elpi Accumulate Db Header <db>` to accumulate just the `Db` declaration
  but no code added after that
- `Elpi File <file> <code>` to name a piece of code without
  requiring an external file
- `Elpi Accumulate File Signature <file>` to accumulate only
  the types declarations from a file. 
- `Elpi Typecheck` is deprecated and is a no-op since `Elpi Accumulate`
  performs type checking incrementally

### HOAS
- new `open-trm` argument for tactics with syntax ````(...)``` and
  `ltac_open_term:(...)`. Open terms can mention free variables.
- new `{{:pat ...}}` quotations inside which `_` is interpreted as a
  wildcard, not as a regular evar.

### API
- Support export locality in `coq.TC.declare-instance`
- `tc-instance` now just carries a priority, no matter if inferred or declared,
  and works for instances added as `Hint Resolve` to the `typclass_instances`
  database

### Build system
- Support dune workspace build with `elpi`

### Misc
- Resolve `.elpi` files based on Coq's resolver. Paths are now expected to be
  of the form `<coq_dir_path>/<rel_path>`, where `<coq_dir_path>` part is a
  logical Coq directory (as mapped with `-Q` or `-R`), and `<rel_path>` is a
  relative path from the corresponding directory.

# [2.2.3] - 30/07/2024

Requires Elpi 1.19.2 and Coq 8.19 or Coq 8.20.

### API
- New `coq.arguments.reset-simplification`
- Change some speedup concerning universes

# [2.2.2] - 15/07/2024

Requires Elpi 1.19.2 and Coq 8.19 or Coq 8.20.

### Packaging
- Fix release script to just publish coq-elpi (and not coq-elpi-tests)
- Fix opam constraints by adding upper bound

# [2.2.1] - 12/07/2024

Requires Elpi 1.19.2 and Coq 8.19 or Coq 8.20.

### Error reporting
- Fix type checking errors on inline code are now reported on the correct line
  in LSP based interfaces

### Build system
- Fix various missing dependencies
- Fix rebuild before installation
- Change CI no more use of docker images
- Change silence `default-output-directory` warning

### Apps/tc
- Change organize the code inside a `tc` namespace

### Apps/derive
- Change do not leak `positive_scope` open

# [2.2.0] - 28/06/2024

Requires Elpi 1.19.2 and Coq 8.19 or Coq 8.20.

### Build system
- Change switch to dune
- New ppx_optcomp to support multiple Coq version
- New no need for dot-merlin-reader, OCaml's language server understands dune

### Apps/tc
- Change supports higher order unification
- Change syntax to register, enable and disable solver
- Change solutions found in Elpi are eta-contracted

### API
- New `coq.debug`
- New `coq.pstring->string` and `coq.string->pstring`
- New `@warn!` attribute for `coq.notation.add-abbreviation`
- New `coq.*.set.min`, `coq.*.set.max`, `coq.*.set.choose`, `coq.*.set.fold`,
  `coq.*.set.partition`
- New `coq.*.map.fold`
- New `coq.env.projection?` and `coq-env.primitive-projection?`

### HOAS
- New `primitive (pstring S)` in Coq 8.20

# Changelog

## [2.1.1] - 15/05/2024

Requires Elpi 1.18.2 and Coq 8.19.

### Commands
- Fix initial synterp state of commands with a synterp phase

## [2.1.0] - 29/03/2024

Requires Elpi 1.18.2 and Coq 8.19.

### Commands
- New `Elpi Accumulate dbname File filename` allows to accumulate a file int a db
- Change `Elpi Db` now only creates (and initialises) a database for the specified phase

### API
- New `coq.parse-attributes` support for the `attlabel` specification,
  see `coq-lib-common.elpi` for its documentation.
- New `coq.goal->pp`
- Replace `coq.replay-all-missing-synterp-actions` by (nestable) groups of actions
- New `coq.begin-synterp-group` and `coq.end-synterp-group` primitives
- New `coq.replay-synterp-action-group` primitive (replaces `coq.replay-all-missing-synterp-actions` in conjunction with a group)
- New `coq.replay-next-synterp-actions` to replay all synterp actions until the next beginning/end of a synterp group
- New `coq.primitive.projection-unfolded` to fold/unfold a primitive projection.
  Note that unfolded primitive projections are still compact terms, but they
  are displayed as `match` expressions and some Ltac code can see that.

## [2.0.2] - 01/02/2024

Requires Elpi 1.18.2 and Coq 8.19.

### API
- Fix `coq.elaborate-*` does not erase the type annotation of `Let`s (regression
  introduced in 2.0.1). This fix may introduce differences in generated names
- Fix `coq.elaborate-*` are not affected anymore by printing options

### Commands
- Fix install the right initial parsing state (the one before any synterp action
  is re-played)

### HOAS
- Fix evar instantiation loss when crossing the elpi/ltac border
- Fix encoding of "definitional classes" (`Class` with no record)
- Fix order of implicit arguments of `Record`

### Misc
- Change requiring `elpi` does not load primitive integers nor primitive floats

### Apps
- TC: avoid declaring options twice (could make vscoq2 fail)
- CS: `cs` now takes a context, a term that is the projection of some structure applied to the parameters of the structure, a term to put a structure on and the solution to return

## [2.0.1] - 29/12/2023

Requires Elpi 1.18.1 and Coq 8.19.

This minor release adds compatibility with Coq 8.19.

## [2.0.0] - 23/12/2023

Requires Elpi 1.18.1 and Coq 8.18.

This major release accommodates for the separation of parsing from execution
of Coq 8.18 enabling Coq-Elpi programs to be run efficiently (and correctly)
under VSCoq 2.0.

### Documentation
- New section about parsing/execution separation in the [Writing commands in Elpi](https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html) tutorial

### Commands
- New `Elpi *` commands understand the `#[phase]` attribute, see the doc in
  the [README](README.md#vernacular-commands) file, and the section
  about the [separation of parsing from execution](README.md#separation-of-parsing-from-execution-of-vernacular-commands)
- New `Elpi Export` understands an `As` clause to rename or alias a program when exported

### API
- Change `coq.elpi.add-predicate` now locality can be changed
- Experimental `coq.toposort` returns a valid topological ordering of the nodes 
  of a graph
- Change `coq.TC.db-for`, now instances are returned sorted wrt their priority
- New `tc-priority`, contains the priority of an instance and if the priority
  has been given by the user or computed by `coq`
- Change `tc-instance`, now the type is `gref -> tc-priority -> tc-instance` i.e. the priority is not an integer anymore
- New `coq.ltac.fresh-id` to generate fresh names in the proof context
- New `@no-tc!` attribute supported by `coq.ltac.call-ltac1`
- New `coq.TC.get-inst-prio` returns the `tc-priority` of an instance
- New `synterp-action` datatype
- New `coq.replay-all-missing-synterp-actions`
- New `coq.replay-synterp-action`
- New `coq.next-synterp-action`
- New `coq.synterp-actions` (parsing phase only)

### Apps 
- New `tc` app providing an implementation of a type class solver written in elpi.
  This app is experimental

## [1.19.3] - 12/10/2023

Requires Elpi 1.16.5 and Coq 8.18.

### Misc

- Fix `Elpi Export` broken when used from VsCoq2

### APIs

- New `ltac1-tactic` opaque data type
- New `tac` argument constructor
- Change `coq.ltac.call-ltac1` now accepts either a string (tactic name) or
  a tactic expression (of type `ltac1-tactic`)
- New `ltac_tactic:(...)` syntax to pass tactic expressions to Elpi tactics
- New `coq.extra-dep` predicate

## [1.19.1] - 30/08/2023

Requires Elpi 1.16.5 and Coq 8.18.

### Misc
- Automate release process

## [1.19.0] - 04/08/2023

Requires Elpi 1.16.5 and Coq 8.18.

### APPS
- New `coercion` app providing `coercion` predicate
  to program coercions (thanks @proux01).
  This app is experimental.

### API
- Removed option `@nonuniform!` as it disappears from Coq 8.18.
  (c.f. https://github.com/coq/coq/pull/17716 )

## [1.18.0] - 27/07/2023

Requires Elpi 1.16.5 and Coq 8.17.

### Doc
- Mention the trace browser for VSCode in the Elpi tutorial.

### API
- New `coq.elpi.accumulate-clauses` takes a list of clauses which share the
  same DB and accumulation site
- New `coq.elpi.add-predicate` to declare the signature of a new predicate into
  a Db
- New `coq.elpi.predicate` to build a term of type `prop` out of a predicate
  name and arguments
- Change `coq.env.global` now relates a term with a gref, instead of working one
  way only
- Change `coq.elpi.accumulate*` generalise clauses over global universe level,
  and error if algebraic levels are present. It used to warn if levels were
  present.
- New `coq.elaborate*skeleton` support the `@no-tc!` option to disable type
  class resolution
- New `@global!` option for `coq.elpi.accumulate*`
- New `coq.env.current-section-path`
- New `coq.TC.db-tc` giving all type classes
- New `coq.reduction.eta-contract`

### HOAS
- Fix evar declarations were (rarely) generated at the wrong depth, possibly
  resulting in variable captures in types containing binders
- Fix `assert false` in evar instantiation readback (eta contraction code was
  incomplete)
- Fix resiliency in case a goal is closed by side effect (was raising fatal
  errors such as "Not a goal" or "Not a variable after goal")
- Change assigning a hole linked to an evar *always* triggers type checking.
  This is necessary even if the term being assigned is well typed since one
  may still need to declare some universe constraints.
- Change propagate type constraints in `Prop` inward (Coq 8.17 only). Eg.
  `Check (T -> _) : Prop` fails in 8.17 since `_` is assumed to be in `Type`.
  We propagate the constraint ourselves across `->`, `/\`, `\/` and `~`.
- Quotations `{{ ... }}` are now parsed by Coq ensuring the end of input is
  reached. Spurious text results in a parse error. For example `{{ f ) }}`
  is no more accepted, as well as `{{ _.x }}`

### Vernacular
- New `Elpi Print` also print the program in `.txt` format

### Runtime
- Change compilation cache able to prevent most of lengthy compilations in
  Hierarchy-Builder for MathComp 2.0. In some cases Coq-Elpi is more picky
  about the order of accumulated files, in particular a file containing
  the spilling of a predicate `{p}` needs to be accumulated after the
  type or mode of `p` is declared

### APPS
- `derive Inductive i {A}` now sets `A` implicit status globally
- `lock Definition f {A}` now sets `A` implicit status globally

## [1.17.1] - 09/03/2023

Requires Elpi 1.16.5 and Coq 8.17.

### API:
- New `coq.int->uint63` and `coq.float->float64`
- Fix bug introduced in 1.17.0 affecting `coq.ltac.call-ltac1`

## [1.17.0] - 13/02/2023

Requires Elpi 1.16.5 and Coq 8.17.

### API
- New `coq.modpath->library`
- New `coq.modtypath->library`
- Fix `coq.env.*` APIs generating inductives, definitions and modules now
  emit metadata in the `.glob` files so that `coqdoc` can generate hyperlinks

### APPS
- Add `NES.{List,Print}`.
- Support relative paths in `NES.{Open,List,Print}`
  (path `_.P` references top-level namespace `P`, paths without a
  leading `_.` are relative to the current namespace)

## [1.16.0] - 10/11/2022

Requires Elpi 1.16.5 and Coq 8.16.

The main change is the `derive` app which must now be loaded
by importing `derive.std` (just loading `derive` won't work).
See the [new derive documentation](apps/derive).

### API
- Change `coq.env.module` and `coq.env.module-type` do not fail if the
  module (type) contains a mutual inductive. The resulting `gref` is going
  to me unusable with most APIs, though.
- Change `coq.env.module` returns a ADT describing the module contents
- Change `coq.gref->path` and `coq.gref->id` do work on `gref` which point
  to mutual inductives.
- New `coq.env.term-dependencies` computing all the `grefs` occurring in a term.
- New `coq.redflag` and `coq.redflags` types for `@redflags!` option understood
  by `coq.reduction.lazy.*` `and coq.reduction.cbv.norm`
- New `coq.env.fresh-global-id`

### APPS
- Change `derive` usage.
  One should now import `From elpi.apps Require Import derive.std`
- Change derivations `eq` and `eqOK` move to `derive.legacy`
- New derivations `eqb` and `eqbOK` subsuming the previous ones

## [1.15.6] - 27-08-2022

Requires Elpi 1.16.5 and Coq 8.16.

- Fix parse error location display for quotation code
- Fix HOAS of inductives with non-uniform parameters

## [1.15.5] - 30-07-2022

Requires Elpi 1.16.5 and Coq 8.16.

- Fix parse error location display for inline code
- Fix HOAS of evars: pruning was not propagated to the type of the evar

## [1.15.4] - 26-07-2022

Requires Elpi 1.16.5 and Coq 8.16.

- Fix lexical analysis inside quotations error location display
- Fix drop of universe constraints attached to automatically generates
  universe levels (eg when `sort (typ X)` is passed to Coq)
- Fix nix CI

## [1.15.3] - 20-07-2022

Requires Elpi 1.16.5 and Coq 8.16.

- Fix parse error location display

## [1.15.2] - 19-07-2022

Requires Elpi 1.16.5 and Coq 8.16.

- API:
  - Fix `coq.env.indt-decl` correctly handles universes in parameters of
    universe polymorphic inductive
  - Fix `coq.typecheck-indt-decl` ignores non uniform parameters to compute
    the universe level of the inductive
  - Fix `coq.elaborate-indt-decl-skeleton` ignores non uniform parameters to
    compute the universe level of the inductive

## [1.15.1] - 16-07-2022

Requires Elpi 1.16.5 and Coq 8.16.

- API:
  - Fix `coq.elaborate*skeleton` does refresh universes
  - New `@keepunivs!` attribute to force skeleton APIs to not
    refresh universes. This is useful to keep a link between
    a universe declaration and the declaration itself but still
    elaborate it
  - Fix Coq-Elpi is reentrant when commands call tactics

## [1.15.0] - 13-07-2022

Requires Elpi 1.16.5 and Coq 8.16.

The main changes are:
- experimental support for universe polymorphism. One can read and write
  universe polymorphic terms and manipulate their constraint declarations.
  Terms now have a new `pglobal` term constructor, akin to `global` but for
  global references to universe polymorphic terms, also carrying a universe
  instance. The attribute `@uinstance!` can be used to pass or retrieve
  a universe instance to/from APIs to access the Coq environment, as in
  `@uinstance! I => coq.env.typeof GR Ty_at_I`.
  The meaning of `@uinstance! I =>` depends if `I` is an unset variable or a
  concrete universe instance. In the former case the API generate a fresh
  universe instance (for `GR`) and assign it to `I`; in the latter case it uses
  the provided universe instance.
  See [coq-builtin](coq-builtin.elpi) for the full documentation
- command arguments are elaborated by Coq (unless told otherwise). As a
  consequence arguments can use the full Coq syntax, including deep pattern
  matching and tactics in terms. Raw arguments are (and will remain) available,
  but don't support that yet

### APPS
- New experimental support for polymorphic definitions in `locker`
- New example of `clearbody` tactic taking a list of names in `eltac`
- Change `derive` sets, *globally*, `Uniform Inductive Parameters`. See
  https://coq.inria.fr/refman/language/core/inductive.html#coq:flag.Uniform-Inductive-Parameters
  for reference. The immediate effect is that inductive types uniform parameters
  don't have to be repeated in the types of the constructors (they can't vary
  anyway). Non-uniform parameters and indexes have to be passed, as usual.
  If the flag is unset by the user `Coq-Elpi` will raise a warning since
  inference of non-uniform parameters is not implemented

### HOAS
- Change arguments to commands are elaborated by Coq by default
- New attribute `#[arguments(raw)]` to get arguments in raw format (as in
  version 1.14 or below)
- Change raw inductive declaration using `|` to mark non-uniform
  parameters is expected to not pass uniform parameters to the inductive
  type (the same behavior applies to elaborated arguments, making the two
  consistent)
- Change `coercion` attribute for record fields now takes values `off`,
  `regular` or `reversible`
- New `pglobal` term constructor carrying a `gref` and a `univ-instance` for
  universe polymorphic terms
- New `upoly-indt-decl` argument type for polymorphic inductive types
  declarations
- New `upoly-const-decl` argument type for polymorphic definitions
- New `upoly-decl` data type for universe parameters declarations, i.e.
  the `@{u1 u2 | u1 < u2}` Coq syntax one can use for inductives or definitions
- New `upoly-decl-cumul` data type for universe parameters declarations, i.e.
  the `@{u1 u2 | u1 < u2}` Coq syntax one can use for cumulative inductives
- Rename `univ` -> `sort` i.e. `(sort S)` is a `term` and `S` can be `prop` or
  `(type U)` where `U` is a `univ`
- New `univ-instance` opaque type to represent how a polymorphic constant is
  instantiated, i.e. `(pglobal GR I)` where `GR` is a `gref` and `I` a
  `univ-instance`
- New `univ.variable` opaque type for `univ` which are not algebraic. This data
  type is used in `upoly-decl` and `upoly-decl-cumul`

### API
- New `coq.env.indc->indt`
- New `coq.env.dependencies` to compute the dependencies of a `gref`
- New `coq.env.transitive-dependencies`
- New `@nonuniform!` and `@reversible!` for `coq.coercion.declare`
- New `@uinstance!` attribute supported by many `coq.env.*` APIs that can be
  used to read/write the universe instance of polymorphic constants. E.g.
  `@uinstance! UI => coq.env.typeof GR Ty` can instantiate `Ty` to `UI` if
  provided or set `UI` to a fresh instance if not
- New `@udecl!` attribute to declare polymorphic constants or inductives,
  like the `@{u1 u2 | u1 < u2}` Coq syntax
- New `@udecl-cumul!` attribute to declare polymorphic inductives,
  like the `@{+u1 u2 | u1 < u2}` Coq syntax
- New `@univpoly!` shorter version of `@udecl!`,
  like the `#[universes(polymorphic)]` Coq syntax (without giving any other
  `@{u1 u2 | u1 < u2}` directive)
- New `@univpoly-cumul!` shorter version of `@udecl-cumul!`, like
  the `#[universes(polymorphic,cumulative)]` Coq syntax
- New `coq.env.global` API to craft a `term` from a `gref`. When used with
  spilling `{coq.env.global GR}` gives either `(global GR)` or `(pglobal GR I)`
  depending on `GR` being universe polymorphic or not. It understands the
  `@unistance!` attribute for both reading or setting `I`
- New `coq.env.univpoly?` to tell if a `gref` is universe polymorphic and how
  many parameters it has
- Change `coq.univ.leq` -> `coq.sort.leq`
- Change `coq.univ.eq` -> `coq.sort.eq`
- Change `coq.univ.sup` -> `coq.sort.sup`
- New `coq.sort.pts-triple` computes the resulting `sort` of a product
- New `coq.univ.constraints` gives all the universe constraints in a first class
  form
- Change `coq.univ.new` does not take a list anymore
- New `coq.univ` to find a global universe
- New `coq.univ.global?` tests if a universe is global
- New `coq.univ.variable` links a `univ` to a `univ.variable` (imposing an
  equality constraint if needed)
- New `coq.univ.variable.constraints` finds all constraints talking about a
  variable
- New `coq.univ.variable.of-term` finds all variables occurring in a term
- New `coq.univ-instance` links a `univ-instance` to a list of of
  `univ.variable`
- New `coq.univ-instance.unify-eq` unifies two `univ-instance`
  (for the same `gref`)
- New `coq.univ-instance.unify-leq` unifies two `univ-instance`
  (for the same `gref`)
- New `coq.univ.set` OCaml's set for `univ`
- New `coq.univ.map` OCaml's map for `univ`
- New `coq.univ.variable.set` OCaml's set for `univ.variable`
- New `coq.univ.variable.map` OCaml's map for `univ.variable`

### Vernacular
- New `Accumulate File <ident>` to be used in tandem with Coq 8.16
  `From <path> Extra Dependency <file> as <ident>`
  
## [1.14.0] - 07-04-2022

Requires Elpi 1.15.0 and Coq 8.15.

### Vernacular
- All `Elpi Bla` commands accept (and ignore with a warning) unknown attributes,
  to be forward compatible

## [1.13.0] - 08-02-2022

Requires Elpi 1.14.1 and Coq 8.15.

### Performance
- New 1 slot cache for context read back to improve the speed of FFI calls
  needing to read back a large `coq_context`
- New `Conversion.t` for `gref` handwritten to minimize allocations
- New terms of the form `(global ...)` are now hashconsed
- New `extra_goals` postprocessing removing `declare-evar/rm-evar` pairs which
  happen naturally writing code like `coq.unify-eq {{ f _ x }} {{ f y _ }}`
  (the `_` are solved immediately, no need to declare them to elpi)

### API
- New `coq.hints.opaque`
- New `coq.hints.set-opaque`
- Change load `coq.ltac.*` also in commands (and not just tactics) so that
  commands can easily turn holes into goals and inhabit them calling regular
  tactics.
- New `coq.hints.add-resolve`
- Fix `coq.option.add` survives the end of a file
- New `coq.env.begin-module-functor`
- New `coq.env.begin-module-type-functor`
- New `coq.env.apply-module-functor`
- New `coq.env.apply-module-type-functor`
- New `coq.inline` with constructors `coq.inline.no`, `coq.inline.at` and
  `coq.inline.default`
- New `@inline-at! N` and `@inline!` macros
- Change `coq.env.add-axiom` honors `@inline` macros

## [1.12.1] - 20-01-2022

Requires Elpi 1.13.6 and Coq 8.15.

### APPS
- `derive Inductive i {A}` now correctly sets `A` implicit status
- `lock Definition f {A}` now correctly sets `A` implicit status

### API
- New `coq.arity->implicits`
- New `coq.indt-decl->implicits`
- New `coq.any-implicit?`

## [1.12.0] - 15-01-2021

Requires Elpi 1.13.6 and Coq 8.15.

### HOAS
- Change `{{ p x }}` is no more interpreted as a primitive projection
  even if `p` is the associated constant
- New `{{ x.(p) }}` is interpreted as a primitive projection if `p` is a
  primitive projection
- New `{{ x.(@p params) }}` is interpreted as a regular projection even
  if `p` is a primitive projection, since primitive projections don't have
  parameters and the user wrote some

### API
- Fix globalization of `arity` inside a section
- New `coq.option` type to access Coq's GOption system (Set/Unset vernaculars)
- New `coq.option.add`
- New `coq.option.get`
- New `coq.option.set`
- New `coq.option.available?`
- New `coq.bind-ind-parameters`

### APPS
- New `locker` app providing `lock` and `mlock` commands

## [1.11.2] - 24-09-2021

Requires Elpi 1.13.6 and Coq 8.14.

### API
- Change `coq.bind-ind-arity` preserves `let`
- New `coq.bind-ind-arity-no-let` to reduce `let`, used in `coq.build-match`
- Fix `coq.build-match` putting `let` bindings in `match` return type
- Change `coq.map-under-fun` preserves `let`

## [1.11.1] - 24-09-2021

Requires Elpi 1.13.6 and Coq 8.13.

### API
- New `coq.env.informative?` to know if a type can be eliminated to build
  a term of sort `Type`
- Fix `coq.warning` is synchronized with Coq's Undo machinery
- Retire the venerable "elpi fails" message, replaced with something more
  precise inviting the user to report a bug: errors should be taken care
  of and reported nicely by the programmer.
- New `coq.uint63->int`
- New `coq.float64->float`
- New `coq.ltac.id-free?` tells if a given ident is already used to denote a
    goal hypothesis, or not.

### Derive
- Fix derivation of induction principles for "data types" in `Prop`
- Add derivation of `param1` for the equality test `eq` with name `t.param1_eq`
- Fix `invert` and `idx2inv` when dealing with containers
- New datatypes from the Coq's prelude are derived in advance, no need to
  to `derive nat` anymore.

## [1.11.0] - 30-06-2021

Requires Elpi 1.13.6 and Coq 8.13.

### HOAS
- New node `proj` of type `projection -> int -> primitive-value` holding the
  projection name (a Coq detail) and the number of the field it projects (0
  based), eg: `primitive (proj _ N)` stands for the projection for the Nth
  constructor field counting parameters.
- Change `cs-instance` carries a `gref`

### API
- New `coq.notation.add-abbreviation-for-tactic` to add a parsing rule
  for a tactic-in-term, along the lines of
    `Notation foo := ltac:(elpi mytactic arguments)`
  but passing `mytactic` the correct `elpi.loc` of invocation.
- New `@pplevel!` attribute to control outermost parentheses in `coq.term->pp`
  and similar
- New `coq.hints.add-mode` like the `Hint Mode` vernacular
- New `coq.hints.modes`
- New `coq.TC.declare-class`
- Deprecate `coq.env.const-opaque?` -> `coq.env.opaque?`
- Deprecate `coq.env.const-primitive?` -> `coq.env.primitive?`
- Deprecate `coq.CS.canonical-projections` -> `coq.env.projections`
- New `coq.env.primitive-projections`
- Change `coq.warning` emits the same warning only once

## [1.10.3] - 18-06-2021

Requires Elpi 1.13.6 and Coq 8.13.

### Lib
- Cleanup `elpi.loc` attribute, which now carries a real loc and not a string.
  Thanks to elpi 1.13.6 we can project out the components without messing
  with regular expressions. Moreover loc are printed in a consistent way on
  Unix and Windows.

## [1.10.2] - 11-06-2021

Requires Elpi 1.13.5 and Coq 8.13.

### API
- Change `coq.gref->path` now (consistently) gives the path without the
  final id, which can be retrieved by `coq.gref->id`.

## [1.10.1] - 24-05-2021

Requires Elpi 1.13.5 and Coq 8.13.

### HOAS
- Fix (reverse) the order of the context argument of `goal`. The head of
  the list is the most recent hypothesis and in the last to be loaded (the
  one with higher precedence) by implication when one writes `Ctx => ...`.
- New `msolve` entry point for (possibly multi goal) tactics

### API
- Fix argument interpretation for `coq.ltac.call-ltac1`, the context is now the
  one of the goal alone (and not the one of the goal plus the current one)
- Rename `coq.ltac.then` to `coq.ltac.all`

## [1.10.0] - 21-05-2021

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
  - `ltac_int:(v)` (for `v` of type `int` or `integer`)
  - `ltac_term:(v)` (for `v` of type `constr` or `open_constr` or `uconstr` or `hyp`)
  - `ltac_(string|int|term)_list:(v)` (for `v` of type `list` of ...)
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
  Here the delimiters `#[` and `]` are chosen for consistency, you can use any
  "delimited" syntax really.
  The usual prefix notation is also possible with the following limitations
  due to a parsing conflicts in the Coq grammar (at the time of writing):
  ```coq
  Tactic Notation "#[" attributes(A) "]" "tac" :=
    ltac_attributes:(A) elpi tac.
  ``` 
  - `#[ att ] tac.` does not parse
  - `(#[ att ] tac).` works
  - `idtac; #[ att ] tac.` works
- Change `-qua.lid` is no more understood as the string `"-qua.lid"` but as
  two strings (when passed to a command, syntax error when passed to a tactic)
  
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
