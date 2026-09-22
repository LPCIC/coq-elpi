Getting started
================

Rocq-Elpi is a Rocq plugin embedding `Elpi
<https://github.com/LPCIC/elpi>`_, an implementation of a dialect of
λProlog, a programming language well suited to manipulate abstract syntax
trees containing binders and unification variables.

Rocq-Elpi lets one define new commands and tactics in Elpi. For that purpose
it provides an embedding of Rocq's terms into λProlog using the
Higher-Order Abstract Syntax approach (`HOAS
<https://en.wikipedia.org/wiki/Higher-order_abstract_syntax>`_). It also
exports to Elpi a comprehensive set of Rocq's primitives, so that one can
print a message, access the environment of theorems and data types, define
a new constant, declare implicit arguments, type class instances, and so
on. For convenience it also provides quotations and anti-quotations for
Rocq's syntax, so that one can write ``{{ nat -> lp:X }}`` in the middle of
an Elpi program instead of the equivalent AST.

Installing
-----------

Rocq-Elpi is available on `opam <https://opam.ocaml.org/>`_ as ``rocq-elpi``::

   opam install rocq-elpi

Once installed, load it in a ``.v`` file with::

   From elpi Require Import elpi.

Tutorials
----------

- :doc:`tutorials/elpi-lang` -- an Elpi tutorial; there is nothing
  Rocq-specific in it even though it uses Rocq to step through the examples.
  Start here if you have never used λProlog or a HOAS-based language
  before.
- :doc:`tutorials/coq-hoas` -- how Rocq terms are represented in Elpi, how
  to inspect them and call Rocq APIs under a context of binders, and how
  holes ("evars") are represented. Assumes familiarity with Elpi.
- :doc:`tutorials/coq-commands` (and :doc:`tutorials/coq-commands-advanced`)
  -- how to write commands, including how to store state across calls via
  Dbs and how to handle command arguments. Assumes familiarity with Elpi
  and the HOAS of Rocq terms.
- :doc:`tutorials/coq-tactics` (and :doc:`tutorials/coq-tactics-advanced`)
  -- how goals and tactics are represented, how to handle tactic arguments,
  and how to define tactic notations. Assumes familiarity with Elpi and the
  HOAS of Rocq terms.

See :doc:`examples/index` for a cookbook of short, self-contained, live-tested
examples, and :doc:`reference/vernacular` for the vernacular command
reference.
