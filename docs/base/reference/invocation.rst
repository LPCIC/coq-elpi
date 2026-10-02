Invocation of Elpi code
=========================

- ``Elpi <qname> <argument>*.`` invokes the ``main`` predicate of the
  ``<qname>`` program passing a possible empty list of arguments. This is
  how you invoke a command.
- ``elpi <qname> <argument>*.`` invokes the ``solve`` predicate of the
  ``<qname>`` program passing a possible empty list of arguments and the
  current goal. This is how you invoke a tactic.
- ``Elpi Export <qname> [As <other-qname>]`` makes it possible to invoke
  command ``<qname>`` (or ``<other-qname>`` if given) without the ``Elpi``
  prefix, or invoke tactic ``<qname>`` in the middle of a term just writing
  ``<qname> args`` instead of ``ltac:(elpi <qname> args)``. Note that in the
  case of tactics, all arguments are considered to be terms. Moreover,
  remember that one can use ``Tactic Notation`` to give the tactic a better
  syntax and a shorter name when used in the middle of a proof script.
  Commands can declare the behavior of starting/ending a proof by,
  respectively, using ``#[proof="begin"] Elpi Export ..`` and
  ``#[proof="end"] Elpi Export ..``. Starting the proof can depend on the
  presence of an attribute, for example
  ``#[proof(begin_if="interactive")] Elpi Export foo`` will make ``foo`` not
  open a proof, while ``#[interactive] foo`` will open a proof. See also the
  ``main-interp-proof`` and ``main-interp-qed`` entry points in
  :doc:`builtins`.

where ``<argument>`` can be:

- a number, e.g. ``3``, represented in Elpi as ``(int 3)``
- a string, e.g. ``"foo"`` or ``bar.baz``, represented in Elpi as
  ``(str "foo")`` and ``(str "bar.baz")``. Rocq keywords and symbols are
  recognized as strings, e.g. ``=>`` requires no quotes. Quotes are
  necessary if the string contains a space or a character that is not
  accepted for qualified identifiers, or if the string is ``Definition``,
  ``Axiom``, ``Record``, ``Structure``, ``Inductive``, ``CoInductive``,
  ``Variant`` or ``Context``.
- a term, e.g. ``(3)`` or ``(f x)``, represented in Elpi as ``(trm ...)``.
  Note that terms always require parentheses, that is ``3`` is a number
  while ``(3)`` is a Rocq term and depending on the context could be a
  natural number (i.e. ``S (S (S O))``) or a ``Z`` or ... See also the
  sections below on terms as arguments and Ltac variables.

Commands also accept the following arguments (the syntax is as close as
possible to the Rocq one: ``[...]`` means optional, ``*`` means 0 or more).
See the ``argument`` data type in :doc:`builtins` for their HOAS encoding.
See also the section on terms as arguments below.

- ``Definition`` *name* *binder*\* [``:`` *term*] ``:=`` *term*
- ``Axiom`` *name* ``:`` *term*
- [ ``Record`` | ``Structure`` ] *name* *binder*\* [``:`` *sort*] ``:=``
  [*name*] ``{`` *name* ``:`` *term* ``;`` \* ``}``
- [ ``Inductive`` | ``CoInductive`` | ``Variant`` ] *name* *binder*\*
  [``|`` *binder*\*] [``:`` *term*] ``:=`` ``|`` *name* *binder*\* ``:`` *term* \*
- ``Context`` *binder*\*

Ltac variables
---------------

Tactics also accept Ltac variables as follows:

- ``ltac_string:(v)`` (for ``v`` of type ``string`` or ``ident``)
- ``ltac_int:(v)`` (for ``v`` of type ``int`` or ``integer``)
- ``ltac_term:(v)`` (for ``v`` of type ``constr`` or ``open_constr`` or
  ``uconstr`` or ``hyp``)
- ``ltac_open_term:(v)`` (for ``v`` of type ``uconstr``)
- ``ltac_(string|int|term|open_term)_list:(v)`` (for ``v`` of type ``list``
  of ...)
- ``ltac_tactic:(t)`` (for ``t`` of type ``tactic``)
- ``ltac_attributes:(v)`` (for ``v`` of type ``attributes``)

For example:

.. code-block:: coq

   Tactic Notation "tac" string(X) ident(Y) int(Z) hyp(T) constr_list(L) simple_intropattern_list(P) uconstr(U) tactic(TA) :=
     elpi tac ltac_string:(X) ltac_string:(Y) ltac_int:(Z) ltac_term:(T) ltac_term_list:(L) ltac_tactic:(intros P) ltac_open_term:(U) ltac_tactic:(TA).

lets one write ``tac "a" b 3 H t1 t2 t3 [|m] u ta`` in any Ltac context.
Arguments are first interpreted by Ltac according to the types declared in
the tactic notation and then injected in the corresponding Elpi argument.
For example ``H`` must be an existing hypothesis, since it is typed with the
``hyp`` Ltac type, but in Elpi it will appear as a term, e.g. ``trm c0``.
Similarly ``t1``, ``t2`` and ``t3`` are checked to be well typed and to
contain no unresolved implicit arguments, since this is what the ``constr``
Ltac type means. If they were typed as ``open_constr`` or ``uconstr``, the
last or both checks would be respectively skipped. In any case they are
passed to the Elpi code as ``trm ...``. Both ``"a"`` and ``b`` are passed to
Elpi as ``str ...``. Argument ``U`` flagged as ``ltac_open_term`` can mention
free variables. The Elpi tactic receives ``open-trm N F`` where ``N`` is the
number of free variables in ``U`` and ``F`` is ``fun x1 => ... fun xN => U``.
Argument ``TA`` is received as ``tac T`` where ``T`` is an (opaque) tactic
that can be called via the ``coq.ltac.*`` APIs. Finally, ``ltac_term:(T)``
and ``(T)`` are *not* synonyms: the former must be used when defining tactic
notations, the latter when invoking elpi tactics directly. ``\`(T)`` can be
used to pass an open term to ``elpi tactic ...``.

Attributes
-----------

Attributes are supported in both commands and tactics. Examples:

- ``#[ att ] Elpi cmd``
- ``#[ att ] cmd`` for a command ``cmd`` exported via ``Elpi Export cmd``
- ``#[ att ] elpi tac``
- ``Tactic Notation ... attributes(A) ... := ltac_attributes:(A) elpi tac``.
  Due to a parsing conflict in Rocq's grammar, at the time of writing this
  code:

  .. code-block:: coq

     Tactic Notation "#[" attributes(A) "]" "tac" :=
       ltac_attributes:(A) elpi tac.

  has the following limitation:

  - ``#[ att ] tac.`` does not parse
  - ``(#[ att ] tac).`` works
  - ``idtac; #[ att ] tac.`` works

Terms as arguments
--------------------

Since version 1.15, terms passed to Elpi commands via ``(term)`` or via a
declaration (like ``Record``, ``Inductive`` ...) are in elaborated format by
default. This means that all Rocq notational facilities are available, like
deep pattern matching, or tactics in terms. One can use the attribute
``#[arguments(raw)]`` to declare a command which instead takes arguments in
raw format. In that case, notations are unfolded, implicit arguments are
expanded (holes ``_`` are added) and lexical analysis is performed (global
names and bound names are identified, holes are applied to bound names in
scope), but deep pattern matching or tactics in terms are not supported, and
in particular type checking/inference is not performed. One can use the
``coq.typecheck`` or ``coq.elaborate-skeleton`` APIs to fill in implicit
arguments and insert coercions on raw terms.

Terms passed to Elpi tactics via tactic notations can be forced to be
elaborated beforehand by declaring the parameters to be of type ``constr``
or ``open_constr``. Arguments of type ``uconstr`` are passed raw.

Testing/debugging
-------------------

- ``Elpi Query [<qname>] <code>`` runs ``<code>`` in the current program (or
  in ``<qname>`` if specified).
- ``Elpi Query [<qname>] <synterp-code> <interp-code>`` runs
  ``<synterp-code>`` in the current (synterp) program (or in ``<qname>`` if
  specified) and ``<interp-code>`` in the current program (or ``<qname>``).
- ``elpi query [<qname>] <string> <argument>*`` runs the ``<string>``
  predicate (that must have the same signature as the default predicate
  ``solve``).
