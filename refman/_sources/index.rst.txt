.. Rocq-Elpi manual master file.
   The full table of contents is built from the toctree directives below.

Rocq-Elpi
==========

`Rocq-Elpi <https://github.com/LPCIC/coq-elpi>`_ embeds `Elpi
<https://github.com/LPCIC/elpi>`_, an implementation of `λProlog
<http://www.lix.polytechnique.fr/~dale/lProlog/>`_, into the Rocq prover. It
lets one write commands, tactics, and even entire plugins in a logic
programming language well suited to manipulate the abstract syntax trees of
Rocq terms, including binders and unification variables.

The `Elpi user manual <https://lpcic.github.io/elpi/>`_ is a separate
document: this manual only gives a short tutorial on Elpi itself, and
defers to it for the full language reference.


.. toctree::
   :maxdepth: 1
   :caption: Tutorials

   getting-started
   tutorials/elpi-lang
   tutorials/coq-hoas
   tutorials/coq-commands
   tutorials/coq-commands-advanced
   tutorials/coq-tactics
   tutorials/coq-tactics-advanced
   tutorials/plugin

.. toctree::
   :maxdepth: 1
   :caption: Reference

   reference/vernacular
   reference/synterp-interp
   reference/invocation
   reference/builtins

.. toctree::
   :maxdepth: 1
   :caption: Examples

   examples/index

.. toctree::
   :maxdepth: 1
   :caption: Applications

   apps
