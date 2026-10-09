Writing tactics in Elpi
============================

.. seealso::
   An `Alectryon-rendered version
   <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html>`_ of
   this tutorial (together with :doc:`coq-tactics-advanced`), from before
   its migration to this manual, is also available.

This tutorial focuses on the implementation of Rocq tactics.

This tutorial assumes the reader is familiar with Elpi and the HOAS
representation of Rocq terms; if it is not the case, please take a look at
these other tutorials first: :doc:`elpi-lang` and :doc:`coq-hoas`.

.. contents::

Defining tactics
--------------------

In Rocq a proof is just a term, and an incomplete proof is just a term
with holes standing for the open goals.

When a proof starts there is just one hole (one goal) and its type
is the statement one wants to prove. Then proof construction makes
progress by instantiation: a term possibly containing holes is
grafted to the hole corresponding to the current goal. What a tactic
does behind the scenes is to synthesize this partial term.

Let's define a simple tactic that prints the current goal.

.. rocqtop:: none reset

   Set Warnings "-elpi.linear-variable".

.. rocqtop:: all

   From elpi Require Import elpi.

   Elpi Tactic show.
   Elpi Accumulate lp:{{

     solve (goal Ctx _Trigger Type Proof _) _ :-
       coq.say "Goal:" Ctx "|-" Proof ":" Type.

   }}.

The tactic declaration is made of 3 parts.

The first one ``Elpi Tactic show.`` sets the current program to ``show``.
Since it is declared as a ``Tactic`` some code is loaded automatically:

* APIs (eg :builtin:`coq.say`) and data types (eg Rocq :type:`term` s) are loaded from
  `coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin.elpi>`_
* some utilities, like :lib:`copy` or :libred:`whd1` are loaded from
  `elpi-tactic-template.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_

The second one ``Elpi Accumulate ...`` loads some extra code.
The ``Elpi Accumulate ...`` family of commands lets one accumulate code
taken from:

* verbatim text ``Elpi Accumulate lp:{{ code }}``
* source files ``Elpi Accumulate File path``
* data bases (Db) ``Elpi Accumulate Db name``

Accumulating code via inline text or file is equivalent, the AST of ``code``
is stored in the .vo file (the external file does not need to be installed).
We invite the reader to look up the description of data bases in the tutorial
about commands.

When some code is accumulated Elpi verifies that the
code does not contain the most frequent kind of mistakes, via some
type checking and linting. Some mistakes are minor and Elpi only warns about
them. You can pass ``-w +elpi.typecheck`` to ``coqc`` to turn these warnings into
errors.

The entry point for tactics is called :builtin:`solve` which maps a :type:`goal`
into a list of :type:`sealed-goal` (representing subgoals).

Tactics written in Elpi can be invoked by prefixing its name with ``elpi``.

.. rocqtop:: all
   :assert: X0 c0 c1

   Lemma tutorial x y  : x + 1 = y.
   elpi show.
   Abort.

In the Elpi code up there :e:`Proof` is the hole for the current goal,
:e:`Type` the statement to be proved and :e:`Ctx` the proof context (the list of
hypotheses). Since we don't assign :e:`Proof` the tactic makes no progress, as
the output above shows: the first line is the proof context, where proof
variables are bound Elpi variables (here :e:`c0` and :e:`c1`), and the context
is a list of predicates holding on them (their type in Rocq). For example:

.. code-block:: elpi

    decl c0 `x` (global (indt «nat»))

asserts that :e:`c0` (pretty printed as ``x``) has type ``nat``.

Then we see that the value of :e:`Proof` is :e:`X0 c0 c1`. This means that the
proof of the current goal is represented by Elpi's variable :e:`X0` and that
the variable has :e:`c0` and :e:`c1` in scope (the proof term can use them).

Finally we see the type of the goal ``x + 1 = y``.

The :e:`_Trigger` component, which we did not print, is a variable that, when
assigned, triggers the elaboration of its value against the type of the goal
and obtains a value for :e:`Proof` this way.

Keeping in mind that the :builtin:`solve` predicate relates one goal to a list of
subgoals, we implement our first tactic which blindly tries to solve the goal.

.. rocqtop:: all

   Elpi Tactic blind.
   Elpi Accumulate lp:{{
     solve (goal _ Trigger _ _ _) [] :- Trigger = {{0}}.
     solve (goal _ Trigger _ _ _) [] :- Trigger = {{I}}.
   }}.

   Lemma test_blind : True * nat.
   Proof.
   split.
   - elpi blind.
   - elpi blind.
   Show Proof.
   Qed.

Since the assignment of a term to :e:`Trigger` triggers its elaboration against
the expected type (the goal statement), assigning the wrong proof term
results in a failure which in turn results in the other rule being tried.

For now, this is all about the low level mechanics of tactics which is
developed further in :doc:`coq-tactics-advanced`.

We now focus on how to better integrate tactics written in Elpi with Ltac.

Integration with Ltac
~~~~~~~~~~~~~~~~~~~~~~~~

For a simple tactic like ``blind`` the list of subgoals is easy to write, since
it is empty, but in general one should collect all the holes in
the value of :e:`Proof` (the checked proof term) and build goals out of them.

There is a family of APIs named after :libtac:`refine`, the mother of all
tactics, in
`elpi-ltac.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_
which does this job for you.

Usually a tactic builds a (possibly partial) term and calls
:libtac:`refine` on it.

Let's rewrite the ``blind`` tactic using this schema.

.. rocqtop:: all

   Elpi Tactic blind2.
   Elpi Accumulate lp:{{
     solve G GL :- refine {{0}} G GL.
     solve G GL :- refine {{I}} G GL.
   }}.

   Lemma test_blind2 : True * nat.
   Proof.
   split.
   - elpi blind2.
   - elpi blind2.
   Qed.

This schema works even if the term is partial, that is if it contains holes
corresponding to missing sub proofs.

Let's write a tactic which opens a few subgoals, for example
let's implement the ``split`` tactic.

.. important::

   Elpi's equality (that is, unification) on Rocq terms corresponds to
   alpha equivalence, we can use that to make our tactic less blind.

The head of a rule for the solve predicate is *matched* against the
goal. This operation cannot assign unification variables in the goal, only
variables in the rule's head.
As a consequence the following rule for ``solve`` is only used when
the statement features an explicit conjunction.

.. rocqtop:: all

   About conj. (* remark the implicit arguments *)

   Elpi Tactic split.
   Elpi Accumulate lp:{{
     solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
       % conj has 4 arguments, but two are implicits
       % (_ are added for them and are inferred from the goal)
       refine {{ conj _ _ }} G GL.

     solve _ _ :-
       % This signals a failure in the Ltac model. A failure
       % in Elpi, that is no more clauses to try, is a fatal
       % error that cannot be caught by Ltac combinators like repeat.
       coq.ltac.fail _ "not a conjunction".
   }}.

   Lemma test_split : exists t : Prop, True /\ True /\ t.
   Proof.
   eexists.
   repeat elpi split. (* The failure is caught by Ltac's repeat *)
   (* Remark that the last goal is left untouched, since
      it did not match the pattern {{ _ /\ _ }}. *)
   all: elpi blind.
   Show Proof.
   Qed.

The tactic ``split`` succeeds twice, stopping on the two identical goals ``True`` and
the one which is an evar of type ``Prop``.

We then invoke ``blind`` on all goals. In the third case the type checking
constraint triggered by assigning ``{{0}}`` to ``Trigger`` fails because
its type ``nat`` is not of sort ``Prop``, so it backtracks and picks ``{{I}}``.

Another common way to build an Elpi tactic is to synthesize a term and
then call some Ltac piece of code finishing the work.

The API :libtac:`coq.ltac.call` invokes some Ltac piece
of code passing to it the desired
arguments. Then it builds the list of subgoals.

Here we pass an integer, which in turn is passed to ``fail``, and a term,
which in turn is passed to ``apply``.

.. rocqtop:: all

   Ltac helper_split2 n t := fail n || apply t.

   Elpi Tactic split2.
   Elpi Accumulate lp:{{
     solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :-
       coq.ltac.call "helper_split2" [int 0, trm {{ conj }}] G GL ok.
     solve _ _ :-
       coq.ltac.fail _ "not a conjunction".
   }}.

   Lemma test_split2 : exists t : Prop, True /\ True /\ t.
   Proof.
   eexists.
   repeat elpi split2.
   all: elpi blind.
   Qed.

Arguments and Tactic Notation
---------------------------------

Elpi tactics can receive arguments. Arguments are received as a list, which
is the last argument of the goal constructor. This suggests that arguments
are attached to the current goal being observed, but we will dive into
this detail later on.

.. rocqtop:: all

   Elpi Tactic print_args.
   Elpi Accumulate lp:{{
     solve (goal _ _ _ _ Args) _ :- coq.say Args.
   }}.

   Lemma test_print_args : True.
   elpi print_args 1 x "a b" (1 = 0).
   Abort.

The convention is that numbers like ``1`` are passed as :e:`int 1`,
identifiers or strings are passed as :e:`str "arg"` and terms
have to be put between parentheses.

.. important:: terms are received in raw format, eg before elaboration

   Indeed the type argument to ``eq`` is a variable.
   One can use APIs like :builtin:`coq.elaborate-skeleton` to infer holes like
   :e:`X0`.

See the :type:`argument` data type
for a detailed description of all the arguments a tactic can receive.

Now let's write a tactic which behaves pretty much like the :libtac:`refine`
one from Rocq, but prints what it does using the API :builtin:`coq.term->string`.

.. rocqtop:: all

   Elpi Tactic refine.
   Elpi Accumulate lp:{{
     solve (goal _ _ Ty _ [trm S] as G) GL :-
       % check S elaborates to T of type Ty (the goal)
       coq.elaborate-skeleton S Ty T ok,

       coq.say "Using" {coq.term->string T}
               "of type" {coq.term->string Ty},

       % since T is already checked, we don't check it again
       refine.no_check T G GL.

     solve (goal _ _ _ _ [trm S]) _ :-
       Msg is {coq.term->string S} ^ " does not fit",
       coq.ltac.fail _ Msg.
   }}.

   Lemma test_refine (P Q : Prop) (H : P -> Q) : Q.
   Proof.
   Fail elpi refine (H).
   elpi refine (H _).
   Abort.

Ltac arguments to Elpi arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is customary to use the Tactic Notation command to attach a nicer syntax
to Elpi tactics.

In particular ``elpi tacname`` accepts as arguments the following `bridges
for Ltac values <https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#syntactic-values>`_ :

* ``ltac_string:(v)`` (for ``v`` of type ``string`` or ``ident``)
* ``ltac_int:(v)`` (for ``v`` of type ``int`` or ``integer``)
* ``ltac_term:(v)`` (for ``v`` of type ``constr`` or ``open_constr`` or ``uconstr`` or ``hyp``)
* ``ltac_(string|int|term)_list:(v)`` (for ``v`` of type ``list`` of ...)

Note that the Ltac type associates some semantics to the action of passing
the arguments. For example ``hyp`` will accept an identifier only if it is
an hypotheses of the context. While ``uconstr`` does not type check the term,
which is the recommended way to pass terms to an Elpi tactic (since it is
likely to be typed anyway by the Elpi tactic).

.. rocqtop:: all

   Tactic Notation "use" uconstr(t) :=
     elpi refine ltac_term:(t).

   Tactic Notation "use" hyp(t) :=
     elpi refine ltac_term:(t).

   Lemma test_use (P Q : Prop) (H : P -> Q) (p : P) : Q.
   Proof.
   use (H _).
   Fail use q.
   use p.
   Qed.

   Tactic Notation "print" uconstr_list_sep(l, ",") :=
     elpi print_args ltac_term_list:(l).

   Lemma test_print (P Q : Prop) (H : P -> Q) (p : P) : Q.
   print P, p, (H p).
   Abort.

Failure
----------

The :builtin:`coq.error` aborts the execution of both
Elpi and any enclosing Ltac context. This failure cannot be caught
by Ltac.

On the contrary the :builtin:`coq.ltac.fail` builtin can be used to
abort the execution of Elpi code in such a way that Ltac can catch it.
This API takes an integer akin to Ltac's fail depth together with
the error message to be displayed to the user.

Library functions of the ``assert!`` family call, by default, :builtin:`coq.error`.
The flag ``@ltacfail! N`` can be set to alter this behavior and turn errors into
calls to ``coq.ltac.fail N``.

.. rocqtop:: all

   Elpi Tactic abort.
   Elpi Accumulate lp:{{
     solve _ _ :- coq.error "uncatchable".
   }}.

   Goal True.
   Fail elpi abort || idtac.
   Abort.

   Elpi Tactic fail.
   Elpi Accumulate lp:{{
     solve (goal _ _ _ _ [int N]) _ :- coq.ltac.fail N "catchable".
   }}.

   Goal True.
   elpi fail 0 || idtac.
   Fail elpi fail 1 || idtac.
   Abort.

Continue with :doc:`coq-tactics-advanced`.
