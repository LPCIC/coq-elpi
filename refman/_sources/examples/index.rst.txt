Examples
========

A cookbook of short, self-contained proofs of concept, each demonstrating one
technique. Every code sample on these pages is run through a real ``rocq
top`` at build time (see :doc:`/index`), so what you read is guaranteed to
actually work.

- :doc:`data-base` stores data and shares it across commands and runs via a Db.
- :doc:`record-expansion` translates a term abstracted over a record into one
  abstracted over the record's components.
- :doc:`record-to-sigma` desugars a record type into iterated sigma types.
- :doc:`fuzzer` mutates a well-typed inductive type while preserving its
  well-typedness, mapping a term and calling the type checker deep inside it.
- :doc:`curry-howard-tactics` builds simple tactics directly as proof terms,
  using Rocq's elaborator.
- :doc:`generalize` abstracts a term over a subterm, like the ``generalize``
  tactic.
- :doc:`abs-evars` closes a term containing holes (evars) by replacing them
  with bound variables.
- :doc:`import-projections` gives short names to a record instance's applied
  projections.
- :doc:`reduction-surgery` fine-tunes ``cbv`` to unfold only the constants
  coming from a given module.
- :doc:`open-terms` implements a ``replace``-like tactic that works on terms
  with variables bound in the goal but not in the proof context.
- :doc:`reflexive-tactic` builds a reflexive tactic solving monoid equalities
  via reification and a Db of known monoids.

.. toctree::
   :maxdepth: 1
   :hidden:

   data-base
   record-expansion
   record-to-sigma
   fuzzer
   curry-howard-tactics
   generalize
   abs-evars
   import-projections
   reduction-surgery
   open-terms
   reflexive-tactic

For adding builtin predicates (implemented in OCaml) to Elpi via a Rocq
plugin, see :doc:`/tutorials/plugin`.
