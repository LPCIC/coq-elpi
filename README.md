[![Actions Status](https://github.com/LPCIC/coq-elpi/workflows/CI/badge.svg)](https://github.com/LPCIC/coq-elpi/actions)
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
For convenience it also provides a quotation and anti-quotation for Coq's
syntax, so that one can write `{{ nat -> lp:X }}` in the middle of a λProlog
program instead of the equivalent AST
``prod `_` (global (indt «Coq.Init.Datatypes.nat»)) X``.

## What is the purpose of all that
In the short term, provide an extension language for Coq well suited to
manipulate terms containing binders. One can already use Elpi to implement
commands and tactics.

In addition to that Elpi extends λProlog with higher order constraints, a
language feature that helps to manipulate terms containing not only binders, but
also unification variables (evars, in Coq's slang). As ongoing research we are
looking forward to express algorithms like higher order unification and type
inference for Coq.

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
the code in an external file and use `Elpi Accumulate File "filename".` instead.

CoqIDE does not handle quotations correctly. The installation process puts
[coq-elpi.lang](etc/coq-elpi.lang)
in a place where CoqIDE can find it.  Then you can select `coq-elpi`
from the menu `Edit -> Preferences -> Colors`.

If you use Vim, we recommend to add the following lines to `~/.vimrc` (in addition to the ones
for [elpi](https://github.com/LPCIC/elpi#syntax-highlight-in-vim))
<details><summary>(click to expand)</summary>
<p>

```vim
"coq-elpi
autocmd FileType lprolog syn keyword coqElpiSpecial fun prod sort let match fix axiom indc indt const prop app
autocmd FileType lprolog syn cluster elpiAntiQuotation contains=elpiAntiQuotationVar,elpiAntiQuotationBound,elpiAntiQuotationTerm
autocmd FileType lprolog syn region elpiAntiQuotationTerm start=+lp:"+ end=+"+ contains=elpiQuotation,lprologVariable,coqElpiSpecial,elpiMacro,lprologSpecial
autocmd FileType lprolog syn match elpiAntiQuotationVar "lp:[A-Z_-]\+"ms=s+3
autocmd FileType lprolog syn match elpiAntiQuotationBound "lp:[a-z_-]\+"
autocmd FileType lprolog hi def link elpiAntiQuotationVar Keyword
autocmd FileType lprolog hi def link elpiAntiQuotationBound Normal
autocmd FileType lprolog hi def link coqElpiSpecial Special
```
</p></details>

</p></details>

<details><summary>Development version (click to expand)</summary><p>

To install the development version one can type
```
opam pin add coq-elpi https://github.com/LPCIC/coq-elpi.git
```
One can also clone this repository and type `make`, but check you have
all the dependencies installed first (see [coq-elpi.opam](coq-elpi.opam)).

</p></details>

## Documentation

### Tutorials

- [The Elpi programming language](examples/tutorial_elpi_lang.v) is an Elpi
  tutorial, there is nothing Coq specific in there even if the tutorial uses Coq
  to step trough the various examples. If you never heard of λProlog or HOAS
  based languages (like Twelf or Beluga) then you are strongly encouraged to
  read this tutorial and have a look at
  [λProlog's home page](http://www.lix.polytechnique.fr/Labo/Dale.Miller/lProlog/)
  for additional documentation. Even if you are familiar with λProlog or HOAS it
  may be worth reading the last sections since they focus on Elpi specific
  features. Last but not least it covers common pitfalls for people with a
  background in functional programming and the tracing mechanisms (useful for
  debugging)
- [Using Elpi to extend Coq](examples/tutorial_coq_elpi.v) focuses on the
  integration of Elpi in Coq, covering the representation of terms and the
  implementation of commands and tactics. It assumes the reader is familiar with
  λProlog
- [Coq-Elpi in 20 minutes](http://www-sop.inria.fr/members/Yves.Bertot/videos/Enrico-Coq-Elpi.mp4)
  video recording of a talk given at the Coq Users and Developers Workshop 2020

### Small examples (proofs of concept)

- [reification](examples/example_reflexive_tactic.v) is the typical use
  case for meta programs: reading the syntax of terms into an inductive
  representing a sub language on which some decision procedure can be
  implemented
- [data bases](examples/example_data_base.v) shows how Elpi programs
  can store data and reuse it across multiple runs
- [record expansion](examples/example_record_expansion.v) sketches a
  program to unpack records in a definition: it  replaces and abstraction over a
  records with abstractions over all of its components
- [record to sigma](examples/example_record_to_sigma.v) sketches a
  program that de-sugars a record type to iterated sigma types
- [fuzzer](examples/example_fuzzer.v) sketches a
  program to alter an inductive type while preserving its well typedness. It
  makes nothing useful per se, but shows how to map a term and call the type
  checker deep inside it.
- [tactics](examples/example_curry_howard_tactics.v) show how to create
  simple tactics by using (proof) terms and the elaborator of Coq

### Applications written in Coq-Elpi

- [Derive](apps/derive/examples/usage.v) shows how to 
  obtain proved equality tests and a few extra gadgets out of
  inductive type declarations. It comes bundled with Coq-Elpi.
- [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) is a
  Coq extension to declare hierarchies of algebraic structures.
- [Namespace Emulation System](apps/NES/examples/usage_NES.v) implements
  most of the features of namespaces (on top of Coq's modules).

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
- `Elpi Program <qname> <code>` lower level primitive letting one crate a
  command/tactic with a custom preamble `<code>`.

- `Elpi Accumulate [<qname>] [<code>|File <filename>|Db <dbname>]` adds code to
  the current program (or `<qname>` if specified). The code can be verbatim,
  from a file or a Db.
- `Elpi Typecheck [<qname>]` typechecks the current program (or `<qname>` if
  specified).
- `Elpi Debug <string>` sets the variable `<string>`, relevant for conditional
  clause compilation (the `:if VARIABLE` clause attribute).
- `Elpi Trace [[<start> <stop>] <predicate-filter>*|Off]` enable/disable
  tracing, eventually limiting it to a specific range of execution steps or
  predicate names.
- `Elpi Bound Steps <number>` limits the number of steps an Elpi program can
  make.
- `Elpi Print <qname> [<string> <filter>*]` prints the program `<qname>` to an
  HTML file named `<qname>.html` (or `<string>` if provided filtering out
  clauses whose file/clause name matches `<filter>`.

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

#### Invocation of Elpi code

<details><summary>(click to expand)</summary>

- `Elpi <qname> <argument>*.` invokes the `main` predicate of the `<qname>`
  program passing a possible empty list of arguments. This is how you invoke a
  command.
- `elpi <qname> <argument>*.` invokes the `solve` predicate of the `<qname>`
  program passing a possible empty list of arguments and the current goal. This
  is how you invoke a tactic.

- `Elpi Export <qname>` makes it possible to invoke command `<qname>` without
  the `Elpi` prefix.

where `<argument>` can be:

- a number, e.g. `3`, represented in Elpi as `(int 3)`
- a string, e.g. `"foo"` or `bar.baz`,  represented in Elpi as `(str "foo")` and
  `(str "bar.baz")`. Coq keywords and symbols are recognized as strings,
  eg `=>` requires no quotes. Quotes are necessary if the string contains
  a space or a character that is not accepted for qualified identifiers or
  if the string is `Definition`, `Axiom`, `Record`, `Inductive` or `Context`.
- a term, e.g. `(3)` or `(f x)`, represented in Elpi as `(trm ...)`. Note that
  terms always require parentheses, that is `3` is a number while `(3)` is a Coq
  term and depending on the context could be a natural number
  (i.e. `S (S (S O))`) or a `Z` or ... See also the section Terms as arguments
  down below.

Commands also accept the following arguments (the syntax is as close as possible
to the Coq one: [...] means optional, * means 0 or more). See the `argument`
data type in `coq-builtin.elpi` for their HOAS encoding. See also the section
Terms as arguments down below.

- `Definition` _name_ _binder_* [`:` _term_] `:=` _term_
- `Axiom` _name_ `:` _term_
- `Record` _name_ _binder_* [`:` _sort_] `:=` [_name_] `{` _name_ `:` _term_ `;` * `}`
- `Inductive` _name_ _binder_* [`|` _binder_*] [`:` _term_] `:=` `|` _name_ _binder_* `:` _term_ *
- `Context` _binder_*

Testing/debugging:

- `Elpi Query [<qname>] <code>` runs `<code>` in the current program (or in
  `<qname>` if specified).
- `elpi query [<qname>] <string> <argument>*` runs the `<string>` predicate
  (that must have the same signature of the default predicate `solve`).

##### Terms as arguments

Terms are passed to Elpi code in raw format. Notations are unfolded, implicit
arguments are expanded (holes `_` are added) and lexical analysis is performed
(global names and bound names are identified, holes are applied to bound
names in scope). Type checking/inference is not performed: the `coq.typecheck`
or `coq.elaborate-skeleton` APIs can be used to fill in implicit arguments and
insert coercions.

</p></details>

#### Relevant files

- [coq-builtin](coq-builtin.elpi) documents the HOAS encoding of Coq terms
  and the API to access Coq
- [elpi-buitin](elpi-builtin.elpi) documents Elpi's standard library, you may
  look here for list processing code
- [coq-lib](elpi/coq-lib.elpi) provides some utilities to manipulate Coq terms;
  it is an addendum to coq-builtin
- [elpi-command-template](elpi/elpi-command-template.elpi) provides the pre-loaded code for
  `Elpi Command`
- [elpi-tactic-template](elpi/elpi-tactic-template.elpi) provides the pre-loaded code for `Elpi Tactic`

#### Organization of the repository

The code of the Coq plugin is at the root of the repository in the [src](src/),
[elpi](elpi/) and [theories](theories/) directories.

The [apps](apps/) directory contains client applications written in Coq-Elpi.
