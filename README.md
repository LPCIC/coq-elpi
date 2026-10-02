[![CI](https://github.com/LPCIC/coq-elpi/actions/workflows/ci.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/ci.yml)
[![Nix 9.1](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-rocq-9.1.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-rocq-9.1.yml)
[![Nix 9.1](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-rocq-9.2.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-rocq-9.2.yml)
[![Nix master](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-rocq-master.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/nix-action-rocq-master.yml)
[![DOC](https://github.com/LPCIC/coq-elpi/actions/workflows/doc.yml/badge.svg)](https://github.com/LPCIC/coq-elpi/actions/workflows/doc.yml)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/253928-Elpi-users.20.26.20devs)
<img align="right" src="https://github.com/LPCIC/coq-elpi/raw/master/etc/rocqy-elpi.png" alt="Rocq-Elpi logo" width="35%" />

### Rocq-Elpi

[Rocq](https://github.com/coq/coq) plugin embedding [Elpi](https://github.com/LPCIC/elpi).

[Elpi](https://github.com/LPCIC/elpi) provides an easy-to-embed implementation
of a dialect of λProlog, a programming language well suited to manipulate
abstract syntax trees containing binders and unification variables.

Rocq-Elpi provides a Rocq plugin that lets one define new commands and tactics in
Elpi. For that purpose it provides an embedding of Rocq's terms into λProlog
using the Higher-Order Abstract Syntax approach
([HOAS](https://en.wikipedia.org/wiki/Higher-order_abstract_syntax)). 

Rocq-Elpi also exports to Elpi a comprehensive set of Rocq's primitives,
so that one can print a message, access the environment of theorems and data
types, define a new constant, declare implicit arguments, type classes
instances, and so on. For convenience it also provides quotations
and anti-quotations for Rocq's syntax, so that one can write `{{ nat -> lp:X }}`
in the middle of an Elpi program instead of the equivalent AST.

Finally Rocq-Elpi provides an FFI to bind OCaml libraries. For
example [apps/json](apps/json) provides access to external data
in json format via the Yojson library, and [apps/xml](apps/xml) does the same
for xml-light.

## What is the purpose of all that
In the short term, provide an extension language for Rocq well suited to
manipulate terms containing binders. One can already use Elpi to implement
commands and tactics.

As ongoing research we are looking forward to express algorithms like higher
order unification and type inference, and to provide an alternative
elaborator for Rocq.

## Installation

The simplest way is to use [OPAM](http://opam.ocaml.org/) and type
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-elpi
opam install rocq-elpi-json # example of optional plugin
```

### Editor Setup

The recommended user interface is [VSRocq](https://github.com/rocq-prover/vsrocq/).
We provide an [extension for vscode](https://github.com/LPCIC/coq-elpi-lang) in the
market place, just look for Elpi. The extension provides syntax hilighting
for both languages even when they are nested via quotations and antiquotations.

<details><summary>Other editors (click to expand)</summary><p>

At the time of writing Proof General does not handle quotations correctly, see ProofGeneral/PG#437.
In particular `Elpi Accumulate lp:{{ .... }}.` is used in tutorials to mix Rocq and Elpi code
without escaping. Rocq-Elpi also accepts `Elpi Accumulate " .... ".` but strings part of the
Elpi code needs to be escaped. Finally, for non-tutorial material, one can always put
the code in an external file declared with `From some.load.path Extra Dependency "filename" as f.`
and use `Elpi Accumulate File f.`.

RocqIDE does handle quotations. The installation process puts
[coq-elpi.lang](etc/coq-elpi.lang)
in a place where RocqIDE can find it.  Then you can select `coq-elpi`
from the menu `Edit -> Preferences -> Colors`.

For Vim users, [Coqtail](https://github.com/whonore/Coqtail) provides syntax
highlighting and handles quotations.

</p></details>

<details><summary>Development version (click to expand)</summary><p>

To install the development version one can type
```
opam pin add rocq-elpi https://github.com/LPCIC/coq-elpi.git
```
One can also clone this repository and type `make`, but check you have
all the dependencies installed first (see [rocq-elpi.opam](rocq-elpi.opam)).

We recommend to look at the [CI setup](.github/workflows) for
ocaml versions being tested. Also, we recommend to install `dot-merlin-reader`
and `ocaml-lsp-server` (version 1.15).

</p></details>

## Documentation

The [reference manual](https://lpcic.github.io/coq-elpi/refman/) includes
tutorials. For a not so short demo, you can look the [Elpi: rule-based
meta-language for Rocq](https://www.youtube.com/watch?v=XjkpA5rVxkM)
  video recording of the keynote at RocqPL25 ([slides & demo files](https://www-sop.inria.fr/members/Enrico.Tassi/coqpl2025/)).

The [reference manual of the Elpi language](https://lpcic.github.io/elpi/) is
a separate document.

## Supported features of Gallina (core calculus of Rocq)

<details><summary>(click to expand)</summary>

- [x] functional core (fun, forall, match, application, let-in, sorts)
- [x] evars (unification variables)
- [x] Inductive types (including mutual)
- [x] CoInductive types (including mutual)
- [x] fixpoints (including mutual)
- [x] cofixpoints (including mutual)
- [x] primitive records
- [x] primitive projections
- [x] primitive integers
- [x] primitive floats
- [x] primitive strings
- [x] primitive arrays (of primitive values)
- [x] universe polymorphism
- [x] modules
- [x] module types
- [x] functor application
- [x] functor definition

</p></details>

## Supported features of Gallina's extensions (extra logical features, APIs)

<details><summary>(click to expand)</summary>

Checked boxes are available, unchecked boxes are planned, missing items are not
planned. This is a high level list, for the details
see [coq-builtin](builtin-doc/coq-builtin.elpi).

- [x] i/o: messages, warnings, errors, Rocq version
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

## Relevant files

- [coq-builtin](builtin-doc/coq-builtin.elpi) documents the HOAS encoding of Rocq terms
  and the API to access Rocq
- [coq-builtin-synterp](builtin-doc/coq-builtin-synterp.elpi) documents APIs to interact with Rocq at parsing time
- [elpi-buitin](builtin-doc/elpi-builtin.elpi) documents Elpi's standard library, you may
  look here for list processing code
- [coq-lib](elpi/coq-lib.elpi) provides some utilities to manipulate Rocq terms;
  it is an addendum to coq-builtin
- [elpi-command-template](elpi/elpi-command-template.elpi) provides the pre-loaded code for `Elpi Command` (execution phase) and `Elpi Tactic`
- [elpi-command-template-synterp](elpi/elpi-command-template-synterp.elpi) provides the pre-loaded code for `Elpi Command` (parsing phase)
- [elpi-tactic-template](elpi/elpi-tactic-template.elpi) provides the pre-loaded code for `Elpi Tactic` (note tactics also load [elpi-command-template](elpi/elpi-command-template.elpi))

## Organization of the repository

The code of the Rocq plugin is at the root of the repository in the [src](src/),
[elpi](elpi/) and [theories](theories/) directories.

The [apps](apps/) directory contains client applications written in Rocq-Elpi.

## License

Rocq-Elpi is free software under the LGPL v2.1 license or any later version.

