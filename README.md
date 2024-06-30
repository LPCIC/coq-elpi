[![Docker CI](https://github.com/LPCIC/coq-elpi/actions/workflows/main.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/main.yml)
[![Nix CI](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-coq-8.19.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-coq-8.19.yml)
[![Nix CI](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-coq-master.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-coq-master.yml)
[![DOC](https://github.com/LPCIC/coq-elpi/actions/workflows/doc.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/doc.yml)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/253928-Elpi-users.20.26.20devs)
<img align="right" src="https://github.com/LPCIC/coq-elpi/raw/master/etc/logo.png" alt="Coq-Elpi logo" width="25%" />

# Coq-Elpi
[Coq](https://github.com/coq/coq) plugin embedding [Elpi](https://github.com/LPCIC/elpi).

## What is Elpi
[Elpi](https://github.com/LPCIC/elpi) provides an easy-to-embed implementation
of a dialect of λProlog, a programming language well suited to manipulate
abstract syntax trees containing binders and unification variables.

## What is Coq-Elpi
Coq-Elpi provides a Coq plugin that lets one define new commands and tactics in
Elpi. For that purpose it provides an embedding of Coq's terms into λProlog
using the Higher-Order Abstract Syntax approach
([HOAS](https://en.wikipedia.org/wiki/Higher-order_abstract_syntax)). It also
exports to Elpi a comprehensive set of Coq's primitives, so that one can
print a message, access the environment of theorems and data types, define a
new constant, declare implicit arguments, type classes instances, and so on.
For convenience it also provides quotations and anti-quotations for Coq's
syntax, so that one can write `{{ nat -> lp:X }}` in the middle of a λProlog
program instead of the equivalent AST.

## What is the purpose of all that
In the short term, provide an extension language for Coq well suited to
manipulate terms containing binders. One can already use Elpi to implement
commands and tactics.
As ongoing research we are
looking forward to express algorithms like higher order unification and type
inference, and to provide an alternative elaborator for Coq.

## Installation

The simplest way is to use [OPAM](http://opam.ocaml.org/) and type
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-elpi
```

### Editor Setup

The recommended user interface is [VSCoq](https://github.com/coq-community/vscoq/).
We provide an [extension for vscode](https://github.com/LPCIC/coq-elpi-lang) in the
market place, just look for Coq Elpi. The extension provides syntax hilighting
for both languages even when they are nested via quotations and antiquotations.

<details><summary>Other editors (click to expand)</summary><p>

At the time of writing Proof General does not handle quotations correctly, see ProofGeneral/PG#437.
In particular `Elpi Accumulate lp:{{ .... }}.` is used in tutorials to mix Coq and Elpi code
without escaping. Coq-Elpi also accepts `Elpi Accumulate " .... ".` but strings part of the
Elpi code needs to be escaped. Finally, for non-tutorial material, one can always put
the code in an external file declared with `From some.load.path Extra Dependency "filename" as f.`
and use `Elpi Accumulate File f.`.

CoqIDE does handle quotations. The installation process puts
[coq-elpi.lang](etc/coq-elpi.lang)
in a place where CoqIDE can find it.  Then you can select `coq-elpi`
from the menu `Edit -> Preferences -> Colors`.

For Vim users, [Coqtail](https://github.com/whonore/Coqtail) provides syntax
highlighting and handles quotations.

</p></details>

<details><summary>Development version (click to expand)</summary><p>

To install the development version one can type
```
opam pin add coq-elpi https://github.com/LPCIC/coq-elpi.git
```
One can also clone this repository and type `make`, but check you have
all the dependencies installed first (see [coq-elpi.opam](coq-elpi.opam)).

We recommend to look at the [CI setup](.github/workflows) for
ocaml versions being tested. Also, we recommend to install `dot-merlin-reader`
and `ocaml-lsp-server` (version 1.15).

</p></details>

## Documentation

### Tutorials

- [The Elpi programming language](https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html) is an Elpi
  tutorial, there is nothing Coq specific in there even if the tutorial uses Coq
  to step trough the various examples. If you never heard of λProlog or HOAS
  based languages (like Twelf or Beluga) then you are strongly encouraged to
  read this tutorial and have a look at
  [λProlog's home page](http://www.lix.polytechnique.fr/Labo/Dale.Miller/lProlog/)
  for additional documentation. Even if you are familiar with λProlog or HOAS it
  may be worth reading the last sections since they focus on Elpi specific
  features. Last but not least it covers common pitfalls for people with a
  background in functional programming and the tracing mechanisms (useful for
  debugging).
- [HOAS of Coq terms](https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html) focuses on how
  Coq terms are represented in Elpi, how to inspect them and call Coq APIs under
  a context of binders, and finally how holes ("evars" in Coq slang) are
  represented. It assumes the reader is familiar with Elpi.
- [Writing commands in Elpi](https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html) focuses on how to
  write commands, in particular how to store a state across calls via so called
  DBs and how to handled command arguments. It assumes the reader is familiar
  with Elpi and the HOAS of Coq terms.
- [Writing tactics in Elpi](https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html) describes how goals
  and tactics are represented, how to handle tactic arguments and finally how
  to define tactic notations. It assumes the reader is familiar with Elpi and
  the HOAS of Coq terms.
- [Coq-Elpi in 20 minutes](https://youtu.be/m60rHnvCJ2o)
  video recording of a talk given at the Coq Users and Developers Workshop 2020.

### Small examples (proofs of concept)

- [reification](examples/example_reflexive_tactic.v) is the typical use
  case for meta programs: reading the syntax of terms into an inductive
  representing a sub language on which some decision procedure can be
  implemented
- [data bases](examples/example_data_base.v) shows how Elpi programs
  can store data and reuse it across multiple runs
- [record expansion](examples/example_record_expansion.v) sketches a
  program to unpack records in a definition: it  replaces an abstraction over a
  records with abstractions over all of its components
- [record to sigma](examples/example_record_to_sigma.v) sketches a
  program that de-sugars a record type to iterated sigma types
- [fuzzer](examples/example_fuzzer.v) sketches a
  program to alter an inductive type while preserving its well typedness. It
  makes nothing useful per se, but shows how to map a term and call the type
  checker deep inside it.
- [tactics](examples/example_curry_howard_tactics.v) show how to create
  simple tactics by using (proof) terms and the elaborator of Coq
- [generalize](examples/example_generalize.v) show how to abstract
  subterms out (one way to skin the cat, there are many)
- [abs_evars](examples/example_abs_evars.v) show how to close a term
  containing holes (evars) with binders
- [record import](examples/example_import_projections.v) gives short names
  to record projections applied to the given record instance.
- [reduction surgery](examples/example_reduction_surgery.v) implements
  a tactic fine tuning cbv with a list of allowed unfoldings taken from a
  module.

### Applications written in Coq-Elpi

- [Derive](apps/derive/examples/usage.v) shows how to 
  obtain proved equality tests and a few extra gadgets out of
  inductive type declarations. See the [README](apps/derive/README.md)
  for the list of derivations. It comes bundled with Coq-Elpi.
- [Locker](apps/locker) lets one hide the computational contents of definitions
  via modules or opaque locks. It comes bundled with Coq-Elpi.
- [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) is a
  Coq extension to declare hierarchies of algebraic structures.
- [Algebra Tactics](https://github.com/math-comp/algebra-tactics/) is a 
  port of the `ring` and `field` tactics to the Mathematical Components
  library.
- [Trakt](https://github.com/ecranceMERCE/trakt) is a generic goal
  preprocessing tool for proof automation tactics in Coq.
- [Namespace Emulation System](apps/NES/examples/usage_NES.v) implements
  most of the features of namespaces (on top of Coq's modules).
- [Dx](https://gitlab.univ-lille.fr/samuel.hym/dx) uses elpi to generate
  an intermediate representation of Coq terms, to be later tranformed into
  C.
- [Coercion](apps/coercion) enable to program coercions in Elpi.
  It comes bundled with Coq-Elpi.

### Quick Reference

In order to load Coq-Elpi use `From elpi Require Import elpi`.

#### Vernacular commands

<details><summary>(click to expand)</summary>

- `Elpi Command <qname>` creates command named `<qname>` containing the preamble
  [elpi-command](elpi/elpi-command-template.elpi).
- `Elpi Tactic <qname>` creates a tactic `<qname>` containing the preamble
  [elpi-tactic](elpi/elpi-tactic-template.elpi).
- `Elpi Db <dbname> <code>` creates a Db (a program that is accumulated into
  other programs). `<code>` is the initial contents of the Db, including the
  type declaration of its constituting predicates.
  It understands the `#[phase]` attribute, see [synterp-vs-interp](README.md#separation-of-parsing-from-execution-of-vernacular-commands).
- `Elpi Program <qname> <code>` lower level primitive letting one crate a
  command/tactic with a custom preamble `<code>`.
- `From some.load.path Extra Dependency <filename> as <fname>`.
- `Elpi Accumulate [<dbname>|<qname>] [<code>|File <fname>|Db <dbname>]`
  adds code to the current program (or `<dbname>` or `<qname>` if specified).
  The code can be verbatim, from a file or a Db.
  File names `<fname>` must have been previously declared with the above command.
  It understands the `#[skip="rex"]` and `#[only="rex"]` which make the command
  a no op if the Coq version is matched (or not) by the given regular expression.
  It understands the `#[phase]` attribute, see [synterp-vs-interp](README.md#separation-of-parsing-from-execution-of-vernacular-commands)
- `Elpi Typecheck [<qname>]` typechecks the current program (or `<qname>` if
  specified).
  It understands the `#[phase]` attribute, see [synterp-vs-interp](README.md#separation-of-parsing-from-execution-of-vernacular-commands)
- `Elpi Debug <string>` sets the variable `<string>`, relevant for conditional
  clause compilation (the `:if VARIABLE` clause attribute).
  It understands the `#[phase]` attribute, see [synterp-vs-interp](README.md#separation-of-parsing-from-execution-of-vernacular-commands)
- `Elpi Trace [[<start> <stop>] <predicate-filter>*|Off]` enable/disable
  tracing, eventually limiting it to a specific range of execution steps or
  predicate names.
  It understands the `#[phase]` attribute, see [synterp-vs-interp](README.md#separation-of-parsing-from-execution-of-vernacular-commands)
- `Elpi Trace Browser` enable/disable
  tracing for Elpi's [trace browser]().
- `Elpi Bound Steps <number>` limits the number of steps an Elpi program can
  make.
- `Elpi Print <qname> [<string> <filter>*]` prints the program `<qname>` to an
  HTML file named `<qname>.html` and a text file called `<qname>.txt`
  (or `<string>` if provided) filtering out clauses whose file or clause-name
  matches `<filter>`.
  It understands the `#[phase]` attribute, see [synterp-vs-interp](README.md#separation-of-parsing-from-execution-of-vernacular-commands)

where:

- `<qname>` is a qualified Coq name, e.g. `derive.eq` or `my_program`.
- `<dbname>` is like `<qname>` but lives in a different namespace. By convention
  `<dbname>` ends in `.db`, e.g. `derive.eq.db`.
- `<code>` is verbatim Elpi code, either `lp:{{ ... }}` or `" ... "` (in the
  latter case, strings delimiters need to be escaped following Coq rules, e.g.
  `lp:{{ coq.say "hello!" }}` becomes `" coq.say ""hello!"" "`).
- `<filename>` is a string containing the path of an external file, e.g.
  `"this_file.elpi"`.
- `<start>` and `<stop>` are numbers, e.g. `17 24`.
- `<predicate-filter>` is a regexp against which the predicate name is matched,
  e.g. `"derive.*"`.

</p></details>

#### Separation of parsing from execution of vernacular commands

<details><summary>(click to expand)</summary>

Since version 8.18 Coq has separate parsing and execution phases,
respectively called synterp and interp.

Since Coq has an extensible grammar the parsing phase is not entirely
performed by the parser: after parsing one sentence Coq evaluates its
synterp action. The synterp actions of a command like `Import A.` are
the subset of its effect which affect parsing, like enabling a notation.
Later, during the execution phase Coq evaluates the its
interp action, which includes effects like putting lemma names in scope or
enables type class instances etc.

Being able to parse an entire document quickly,
without actually executing any sentence, is important for developing reactive
user interfaces, but requires some extra work when defining new commands,
in particular to separate their synterp actions from their interp ones.
Each command defined with Coq-Elpi is split into two programs,
one running during the parsing phase and the other one during the execution
phase.

##### Declaration of synterp actions

Each `Elpi Command` internally declares two programs with the same name.
One to be run while the Coq document is parsed, the synterp-command,
and the other one while it is executed, the interp command.
`Elpi Accumulate`, by default, adds code to the interp-command.
The `#[phase]` attribute can be used to accumulate code to the synterp-command
or to both commands. `Elpi Typecheck` checks both commands.

Each `Elpi Db` internally declares one db, by default for the interp phase.
The `#[phase]` attribute can be used crate a database for the synterp phase,
or for both phases. Note that databases for the two phases are distinct, no
data is shared among them. In particular the `coq.elpi.accumulate*` API exists
in both phases and only acts on data bases for the current phase.

##### The alignment of phases

All synterp actions, i.e. calls to APIs dealing with modules and sections
like begin/end-module or import/export, have to happen at *both* synterp and
interp time and *in the same order*.

In order to do so, the synterp-command may need to communicate data to the
corresponding interp-command. There are two ways for doing so.

The first one is to use, as the main entry points, the following ones:
```
pred main-synterp i:list argument, o:any.
pred main-interp i:list argument, i:any.
```
Unlike `main` the former outputs a datum while the latter receives it in input.
During the synterp phase the API `coq.synterp-actions` lists the actions
performed so far. An excerpt from the [coq-builtin-synterp](builtin-doc/coq-builtin-synterp.elpi) file:
```
% Action executed during the parsing phase (aka synterp)
kind synterp-action type.
type begin-module id -> synterp-action.
type end-module modpath -> synterp-action.
```
The synterp-command can output data of that type, but also any other data it
wishes.

The second way to communicate data is implicit, but limited to synterp actions.
Such synterp actions can be recorded into (nested) groups whose structure is
declared using well-bracketed calls to predicates `coq.begin-synterp-group`
and `coq.end-synterp-group` in the synterp phase. In the interp phase, one can
then use predicate `coq.replay-synterp-action-group` to replay all the synterp
actions of the group with the given name at once.

In the case where one wishes to interleave code between the actions of a given
group, it is also possible to match the synterp group structure at interp, via
`coq.begin-synterp-group` and `coq.end-synterp-group`. Individual actions that
are contained in the group then need to be replayed individually.

One can use `coq.replay-next-synterp-actions` to replay all synterp actions
until the next beginning/end of a synterp group. However, this is discouraged
in favour of using groups explicitly, as this is more modular. Code that used
to rely on the now-removed `coq.replay-all-missing-synterp-actions` predicate
can rely on `coq.replay-next-synterp-actions` instead, but this is discouraged
in favour of using groups explicitly)

##### Syntax of the `#[phase]` attribute

- `#[phase="ph"]` where `"ph"` can be `"parsing"`,
  `"execution"` or `"both"`
- `#[synterp]` is a shorthand for `#[phase="parsing"]`
- `#[interp]` is a shorthand for `#[phase="execution]`

</p></details>

#### Invocation of Elpi code

<details><summary>(click to expand)</summary>

- `Elpi <qname> <argument>*.` invokes the `main` predicate of the `<qname>`
  program passing a possible empty list of arguments. This is how you invoke a
  command.
- `elpi <qname> <argument>*.` invokes the `solve` predicate of the `<qname>`
  program passing a possible empty list of arguments and the current goal. This
  is how you invoke a tactic.

- `Elpi Export <qname> [As <other-qname>]` makes it possible to invoke
  command `<qname>` (or `<other-qname>` if given) without
  the `Elpi` prefix or invoke tactic `<qname>` in the middle of a term just
  writing `<qname> args` instead of `ltac:(elpi <qname> args)`. Note that in
  the case of tactics, all arguments are considered to be terms.
  Moreover, remember that one can use `Tactic Notation` to give the tactic a
  better syntax and a shorter name when used in the middle of a proof script.

where `<argument>` can be:

- a number, e.g. `3`, represented in Elpi as `(int 3)`
- a string, e.g. `"foo"` or `bar.baz`,  represented in Elpi as `(str "foo")` and
  `(str "bar.baz")`. Coq keywords and symbols are recognized as strings,
  eg `=>` requires no quotes. Quotes are necessary if the string contains
  a space or a character that is not accepted for qualified identifiers or
  if the string is `Definition`, `Axiom`, `Record`, `Structure`, `Inductive`,
  `CoInductive`, `Variant` or `Context`.
- a term, e.g. `(3)` or `(f x)`, represented in Elpi as `(trm ...)`. Note that
  terms always require parentheses, that is `3` is a number while `(3)` is a Coq
  term and depending on the context could be a natural number
  (i.e. `S (S (S O))`) or a `Z` or ... See also the section Terms as arguments
  down below, and the syntax for Ltac variables down below.

Commands also accept the following arguments (the syntax is as close as possible
to the Coq one: [...] means optional, * means 0 or more). See the `argument`
data type in `coq-builtin.elpi` for their HOAS encoding. See also the section
Terms as arguments down below.

- `Definition` _name_ _binder_* [`:` _term_] `:=` _term_
- `Axiom` _name_ `:` _term_
- [ `Record` | `Structure` ] _name_ _binder_* [`:` _sort_] `:=` [_name_] `{` _name_ `:` _term_ `;` * `}`
- [ `Inductive` | `CoInductive` | `Variant` ] _name_ _binder_* [`|` _binder_*] [`:` _term_] `:=` `|` _name_ _binder_* `:` _term_ *
- `Context` _binder_*

##### Ltac Variables

Tactics also accept Ltac variables as follows:
- `ltac_string:(v)` (for `v` of type `string` or `ident`)
- `ltac_int:(v)` (for `v` of type `int` or `integer`)
- `ltac_term:(v)` (for `v` of type `constr` or `open_constr` or `uconstr` or `hyp`)
- `ltac_(string|int|term)_list:(v)` (for `v` of type `list` of ...)
- `ltac_tactic:(t)` (for `t` of type `tactic_expr`)
- `ltac_attributes:(v)` (for `v` of type `attributes`)
For example:
```coq
Tactic Notation "tac" string(X) ident(Y) int(Z) hyp(T) constr_list(L) simple_intropattern_list(P) :=
  elpi tac ltac_string:(X) ltac_string:(Y) ltac_int:(Z) ltac_term:(T) ltac_term_list:(L) ltac_tactic:(intros P).
```
lets one write `tac "a" b 3 H t1 t2 t3 [|m]` in any Ltac context.
Arguments are first interpreted by Ltac according to the types declared
in the tactic notation and then injected in the corresponding Elpi argument.
For example `H` must be an existing hypothesis, since it is typed with
the `hyp` Ltac type, but in Elpi it will appear as a term, eg `trm c0`.
Similarly `t1`, `t2` and `t3` are checked to be well typed and to contain no
unresolved implicit arguments, since this is what the `constr` Ltac type means
If they were typed as `open_constr` or `uconstr`, the last or both checks would
be respectively skipped. In any case they are passed to the Elpi code as `trm ...`.
Both `"a"` and `b` are passed to Elpi as `str ...`.
Finally, `ltac_term:(T)` and `(T)` are *not* synonyms: but the former must be used
when defining tactic notations, the latter when invoking elpi tactics directly.

##### Attributes

Attributes are supported in both commands and tactics. Examples:
- `#[ att ] Elpi cmd`
- `#[ att ] cmd` for a command `cmd` exported via `Elpi Export cmd`
- `#[ att ] elpi tac`
- `Tactic Notation ... attributes(A) ... := ltac_attributes:(A) elpi tac`.
  Due to a parsing conflict in Coq grammar, at the time of writing this code:
  ```coq
  Tactic Notation "#[" attributes(A) "]" "tac" :=
    ltac_attributes:(A) elpi tac.
  ``` 
  has the following limitation:
  - `#[ att ] tac.` does not parse
  - `(#[ att ] tac).` works
  - `idtac; #[ att ] tac.` works

##### Terms as arguments

Since version 1.15, terms passed to Elpi commands code via `(term)` or via a
declaration (like `Record`, `Inductive` ...) are in elaborated format by
default. This means that all Coq notational facilities are available, like
deep pattern matching, or tactics in terms.
One can use the attribute `#[arguments(raw)]` to declare a command which instead
takes arguments in raw format. In that case, notations are unfolded,
implicit arguments are expanded (holes `_` are added) and lexical analysis is
performed (global names and bound names are identified, holes are applied
to bound names in scope), but deep pattern matching or tactics in terms are not
supported, and in particular type checking/inference is not performed.
Once can use the `coq.typecheck` or `coq.elaborate-skeleton` APIs
to fill in implicit arguments and insert coercions on raw terms.

Terms passed to Elpi tactics via tactic notations can be forced to be elaborated
beforehand by declaring the parameters to be of type `constr` or `open_constr`.
Arguments of type `uconstr` are passed raw.

##### Testing/debugging:

- `Elpi Query [<qname>] <code>` runs `<code>` in the current program (or in
  `<qname>` if specified).
- `Elpi Query [<qname>] <synterp-code> <interp-code>` runs
  `<synterp-code>` in the current (synterp) program (or in
`<qname>` if specified) and `<interp-code>` in the current program (or `<qname>`).
- `elpi query [<qname>] <string> <argument>*` runs the `<string>` predicate
  (that must have the same signature of the default predicate `solve`).

</p></details>

#### Supported features of Gallina (core calculus of Coq)

<details><summary>(click to expand)</summary>

- [x] functional core (fun, forall, match, application, let-in, sorts)
- [x] evars (unification variables)
- [x] single Inductive and CoInductive types (including parameters, non-uniform
      parameters, indexes)
- [ ] mutual Inductive and CoInductive types
- [x] fixpoints
- [ ] mutual fixpoints
- [ ] cofixpoints
- [x] primitive records
- [x] primitive projections
- [x] primitive integers
- [x] primitive floats
- [ ] primitive arrays
- [x] universe polymorphism
- [x] modules
- [x] module types
- [x] functor application
- [x] functor definition

</p></details>

#### Supported features of Gallina's extensions (extra logical features, APIs)

<details><summary>(click to expand)</summary>

Checked boxes are available, unchecked boxes are planned, missing items are not
planned. This is a high level list, for the details
see [coq-builtin](builtin-doc/coq-builtin.elpi).

- [x] i/o: messages, warnings, errors, Coq version
- [x] logical environment: read, write, locate
  + [x] dependencies between objects
- [x] type classes database: read, write
  + [ ] take over resolution
- [x] canonical structures database: read, write
  + [ ] take over resolution
- [x] coercions database: read, write
- [x] sections: open, close
- [x] scope management: import, export
- [x] hints: mode, opaque, resolve, strategy
- [x] arguments: implicit, name, scope, simpl
- [x] abbreviations: read, write, locate
- [x] typing and elaboration
- [x] unification
- [x] reduction: `lazy`, `cbv`, `vm`, `native`
  - [x] flags for `lazy` and `cbv`
- [x] ltac1: bridge to call ltac1 code, mono and multi-goal tactics
- [x] option system: get, set, add
- [x] pretty printer: boxes, printing width
- [x] attributes: read

</p></details>

#### Relevant files

- [coq-builtin](builtin-doc/coq-builtin.elpi) documents the HOAS encoding of Coq terms
  and the API to access Coq
- [coq-builtin-synterp](builtin-doc/coq-builtin-synterp.elpi) documents APIs to interact with Coq at parsing time
- [elpi-buitin](builtin-doc/elpi-builtin.elpi) documents Elpi's standard library, you may
  look here for list processing code
- [coq-lib](elpi/coq-lib.elpi) provides some utilities to manipulate Coq terms;
  it is an addendum to coq-builtin
- [elpi-command-template](elpi/elpi-command-template.elpi) provides the pre-loaded code for `Elpi Command` (execution phase)
- [elpi-command-template-synterp](elpi/elpi-command-template-synterp.elpi) provides the pre-loaded code for `Elpi Command` (parsing phase)
- [elpi-tactic-template](elpi/elpi-tactic-template.elpi) provides the pre-loaded code for `Elpi Tactic`

#### Organization of the repository

The code of the Coq plugin is at the root of the repository in the [src](src/),
[elpi](elpi/) and [theories](theories/) directories.

The [apps](apps/) directory contains client applications written in Coq-Elpi.
