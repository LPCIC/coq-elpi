Separation of parsing from execution
=====================================

Since version 8.18 Rocq has separate parsing and execution phases,
respectively called synterp and interp.

Since Rocq has an extensible grammar the parsing phase is not entirely
performed by the parser: after parsing one sentence Rocq evaluates its
synterp action. The synterp actions of a command like ``Import A.`` are the
subset of its effect which affect parsing, like enabling a notation. Later,
during the execution phase Rocq evaluates its interp action, which includes
effects like putting lemma names in scope or enabling type class instances
etc.

Being able to parse an entire document quickly, without actually executing
any sentence, is important for developing reactive user interfaces, but
requires some extra work when defining new commands, in particular to
separate their synterp actions from their interp ones. Each command defined
with Rocq-Elpi is split into two programs, one running during the parsing
phase and the other one during the execution phase.

Declaration of synterp actions
-------------------------------

Each ``Elpi Command`` internally declares two programs with the same name.
One to be run while the Rocq document is parsed, the synterp-command, and the
other one while it is executed, the interp-command. ``Elpi Accumulate``, by
default, adds code to the interp-command. The ``#[phase]`` attribute can be
used to accumulate code to the synterp-command or to both commands.
``Elpi Typecheck`` checks both commands.

Each ``Elpi Db`` internally declares one db, by default for the interp
phase. The ``#[phase]`` attribute can be used to create a database for the
synterp phase, or for both phases. Note that databases for the two phases are
distinct, no data is shared among them. In particular the
``coq.elpi.accumulate*`` API exists in both phases and only acts on data
bases for the current phase.

The alignment of phases
-------------------------

All synterp actions, i.e. calls to APIs dealing with modules and sections
like begin/end-module or import/export, have to happen at *both* synterp and
interp time and *in the same order*.

In order to do so, the synterp-command may need to communicate data to the
corresponding interp-command. There are two ways for doing so.

The first one is to use, as the main entry points, the following ones:

.. code-block:: elpi

   pred main-synterp list argument -> any.
   pred main-interp list argument, any.

Unlike ``main`` the former outputs a datum while the latter receives it in
input. During the synterp phase the API ``coq.synterp-actions`` lists the
actions performed so far. An excerpt from the `coq-builtin-synterp
<https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin-synterp.elpi>`_
file (see :doc:`builtins`):

.. code-block:: elpi

   % Action executed during the parsing phase (aka synterp)
   data synterp-action.
   symb begin-module : id -> synterp-action.
   symb end-module : modpath -> synterp-action.

The synterp-command can output data of that type, but also any other data it
wishes.

The second way to communicate data is implicit, but limited to synterp
actions. Such synterp actions can be recorded into (nested) groups whose
structure is declared using well-bracketed calls to predicates
``coq.begin-synterp-group`` and ``coq.end-synterp-group`` in the synterp
phase. In the interp phase, one can then use predicate
``coq.replay-synterp-action-group`` to replay all the synterp actions of the
group with the given name at once.

In the case where one wishes to interleave code between the actions of a
given group, it is also possible to match the synterp group structure at
interp, via ``coq.begin-synterp-group`` and ``coq.end-synterp-group``.
Individual actions that are contained in the group then need to be replayed
individually.

One can use ``coq.replay-next-synterp-actions`` to replay all synterp
actions until the next beginning/end of a synterp group. However, this is
discouraged in favour of using groups explicitly, as this is more modular.
Code that used to rely on the now-removed
``coq.replay-all-missing-synterp-actions`` predicate can rely on
``coq.replay-next-synterp-actions`` instead, but this is discouraged in
favour of using groups explicitly.

Syntax of the ``#[phase]`` attribute
--------------------------------------

- ``#[phase="ph"]`` where ``"ph"`` can be ``"parsing"``, ``"execution"`` or
  ``"both"``
- ``#[synterp]`` is a shorthand for ``#[phase="parsing"]``
- ``#[interp]`` is a shorthand for ``#[phase="execution"]``
