(*|

Tutorial on Coq tactics
***********************

:author: Enrico Tassi

.. include:: ../etc/tutorial_style.rst

..
   Elpi is an extension language that comes as a library
   to be embedded into host applications such as Coq.

   Elpi is a variant of λProlog enriched with constraints.
   λProlog is a programming language designed to make it easy
   to manipulate abstract syntax trees containing binders.
   Elpi extends λProlog with programming constructs that are
   designed to make it easy to manipulate abstract syntax trees
   containing metavariables (also called unification variables, or
   evars in the Coq jargon).

   This software, "coq-elpi", is a Coq plugin embedding Elpi and
   exposing to the extension language Coq spefic data types (e.g. terms)
   and API (e.g. to declare a new inductive type).

   In order to get proper syntax highlighting using VSCode please install the
   "gares.coq-elpi-lang" extension. In CoqIDE please chose "coq-elpi" in
   Edit -> Preferences -> Colors.

   
This tutorial focuses on the implementation of Coq tactics.

This tutorial assumes the reader is familiar with Elpi and the HOAS
representation of Coq terms; if it is not the case, please take a look at
these other tutorials first:
`Elpi tutorial <https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html>`_
and `Coq HOAS tutorial <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html>`_.

.. contents::

================
Defining tactics
================

In Coq a proof is just a term, and an incomplete proof is just a term
with holes standing for the open goals.

When a proof starts there is just one hole (one goal) and its type
is the statement one wants to prove. Then proof construction makes
progress by instantiation: a term possibly containing holes is
grafted to the hole corresponding to the current goal. What a tactic
does behind the scenes is to synthesize this partial term.

Let's define a simple tactic that prints the current goal.

|*)

From elpi Require Import elpi.

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type.

}}.
Elpi Typecheck.

(*|

The tactic declaration is made of 3 parts.
     
The first one `Elpi Tactic show.` sets the current program to `show`.
Since it is declared as a `Tactic` some code is loaded automatically:

* APIs (eg :builtin:`coq.say`) and data types (eg Coq :type:`term` s) are loaded from
  `coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi>`_
* some utilities, like :lib:`copy` or :libred:`whd1` are loaded from
  `elpi-command-template.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi>`_
  
  
The second one `Elpi Accumulate ...` loads some extra code.
The `Elpi Accumulate ...` family of commands lets one accumulate code
taken from:

* verbatim text `Elpi Accumulate lp:{{ code }}`
* source files `Elpi Accumulate File path`
* data bases (Db) `Elpi Accumulate Db name`

Accumulating code via inline text or file is equivalent, the AST of `code`
is stored in the .vo file (the external file does not need to be installed).
We invite the reader to look up the description of data bases in the tutorial
about commands.
  
Once all the code is accumulated `Elpi Typecheck` verifies that the
code does not contain the most frequent kind of mistakes. This command
considers some mistakes minor and only warns about them. You can
pass `-w +elpi.typecheck` to `coqc` to turn these warnings into errors.
  
The entry point for tactics is called :builtin:`solve` which maps a :type:`goal`
into a list of :type:`sealed-goal` (representing subgoals).
  
Tactics written in Elpi can be invoked by prefixing its name with `elpi`.

|*)

Lemma tutorial x y  : x + 1 = y.
elpi show. (* .in .messages *)
Abort.

(*|

In the Elpi code up there :e:`Proof` is the hole for the current goal,
:e:`Type` the statement to be proved and :e:`Ctx` the proof context (the list of
hypotheses). Since we don't assign :e:`Proof` the tactic makes no progess.
Elpi prints somethinglike this:

.. mquote:: .s(elpi).msg{Goal:*X0 c0 c1*}
   :language: text

The first line is the proof context:
proof variables are bound Elpi variables (here :e:`c0` and :e:`c1`), the context
is a list of predicates holding on them (their type in Coq). For example:

.. code::

    decl c0 `x` (global (indt «nat»))

asserts that :e:`c0` (pretty printed as `x`) has type `nat`.

Then we see that the value of :e:`Proof` is :e:`X0 c0 c1`. This means that the
proof of the current goal is represented by Elpi's variable :e:`X0` and that
the variable has :e:`c0` and :e:`c1` in scope (the proof term can use them).

Finally we see the type of the goal `x + 1 = y`.

The :e:`_Trigger` component, which we did not print, is a variable that, when
assigned, trigger the elaboration of its value against the type of the goal
and obtains a value for :e:`Proof` this way.

Keeping in mind that the :builtin:`solve` predicate relates one goal to a list of
subgoals, we implement our first tactic which blindly tries to solve the goal.

|*)

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{0}}.
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{I}}.
}}.
Elpi Typecheck.

Lemma test_blind : True * nat.
Proof. (* .in *)
split.
- elpi blind.
- elpi blind.
Show Proof. (* .in .messages *)
Qed.

(*|

Since the assignment of a term to :e:`Trigger` triggers its elaboration against
the expected type (the goal statement), assigning the wrong proof term
results in a failure which in turn results in the other rule being tried.

Assigning :e:`Proof` directly is *unsound* in the sense that no automatic check
is performed.

|*)

Elpi Tactic blind_bad.
Elpi Accumulate lp:{{
  solve (goal _ _ _ Proof _) [] :- Proof = {{0}}.
  solve (goal _ _ _ Proof _) [] :- Proof = {{I}}.
}}.
Elpi Typecheck.
(*
Lemma test_blind_bad : True * nat.
Proof. (* .in *)
split.
- elpi blind_bad.
- elpi blind_bad.
Show Proof. (* .in .messages *)
Fail Qed.  (* .fails *)
Abort.
*)

(*|

For now, this is all about the low level mechanics of tactics which is
developed further in the section `The-proof-engine`_.

We now focus on how to better integrate tactics written in Elpi with Ltac.

---------------------
Integration with Ltac
---------------------

For a simple tactic like `blind` the list of subgoals is easy to write, since
it is empty, but in general one should collect all the holes in
the value of :e:`Proof` (the checked proof term) and build goals out of them.

There is a family of APIs named after :libtac:`refine`, the mother of all
tactics, in 
`elpi-ltac.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_
which does this job for you.

Usually a tactic builds a (possibly partial) term and calls
:libtac:`refine` on it.

Let's rewrite the `blind` tactic using this schema.

|*)


Elpi Tactic blind2.
Elpi Accumulate lp:{{
  solve G GL :- refine {{0}} G GL.
  solve G GL :- refine {{I}} G GL.
}}.
Elpi Typecheck.

Lemma test_blind2 : True * nat.
Proof. (* .in *)
split.
- elpi blind2.
- elpi blind2.
Qed.

(*|

This schema works even if the term is partial, that is if it contains holes
corresponding to missing sub proofs.

Let's write a tactic which opens a few subgoals, for example
let's implement the `split` tactic.

.. important::

   Elpi's equality (that is, unification) on Coq terms corresponds to
   alpha equivalence, we can use that to make our tactic less blind.

The head of a rule for the solve predicate is *matched* against the
goal. This operation cannot assign unification variables in the goal, only
variables in the rule's head.
As a consequence the following rule for `solve` is only used when
the statement features an explicit conjunction.

|*)

About conj. (* remak the implicit arguments *)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    % conj has 4 arguments, but two are implicits
    % (_ are added for them and are inferred from the goal)
    refine {{ conj _ _ }} G GL.

  solve _ _ :-
    % This signals a failure in the Ltac model. A failure
    % in Elpi, that is no more cluases to try, is a fatal
    % error that cannot be catch by Ltac combinators like repeat.
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split : exists t : Prop, True /\ True /\ t.
Proof. (* .in *)
eexists.
repeat elpi split. (* The failure is catched by Ltac's repeat *)
(* Remark that the last goal is left untouched, since
   it did not match the pattern {{ _ /\ _ }}. *)
all: elpi blind.
Show Proof. (* .in .messages *)
Qed.

(*|

The tactic `split` succeeds twice, stopping on the two identical goals `True` and
the one which is an evar of type `Prop`.

We then invoke `blind` on all goals. In the third case the type checking
constraint triggered by assigning `{{0}}` to `Trigger` fails because
its type `nat` is not of sort `Prop`, so it backtracks and picks `{{I}}`.

Another common way to build an Elpi tactic is to synthesize a term and
then call some Ltac piece of code finishing the work.

The API :libtac:`coq.ltac.call` invokes some Ltac piece
of code passing to it the desired
arguments. Then it builds the list of subgoals.

Here we pass an integer, which in turn is passed to `fail`, and a term,
which is turn is passed to `apply`.

|*)

Ltac helper_split2 n t := fail n || apply t.

Elpi Tactic split2.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :-
    coq.ltac.call "helper_split2" [int 0, trm {{ conj }}] G GL.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split2 : exists t : Prop, True /\ True /\ t.
Proof. (* .in *)
eexists.
repeat elpi split2.
all: elpi blind.
Qed.

(*|

=============================
Arguments and Tactic Notation
=============================

Elpi tactics can receive arguments. Arguments are received as a list, which
is the last argument of the goal constructor. This suggests that arguments
are attached to the current goal being observed, but we will dive into
this detail later on.

|*)

Elpi Tactic print_args.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ Args) _ :- coq.say Args.
}}.
Elpi Typecheck.

Lemma test_print_args : True. (* .in *)
elpi print_args 1 x "a b" (1 = 0). (* .in .messages *)
Abort.

(*|

The convention is that numbers like `1` are passed as :e:`int 1`,
identifiers or strings are passed as :e:`str "arg"` and terms
have to be put between parentheses. 

.. important:: terms are received in raw format, eg before elaboration

   Indeed the type argument to `eq` is a variable.
   One can use APIs like :builtin:`coq.elaborate-skeleton` to infer holes like
   :e:`X0`.

See the :type:`argument` data type
for a detailed decription of all the arguments a tactic can receive.

Now let's write a tactic which behaves pretty much like the :libtac:`refine`
one from Coq, but prints what it does using the API :builtin:`coq.term->string`.

|*)

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
Elpi Typecheck.

Lemma test_refine (P Q : Prop) (H : P -> Q) : Q.
Proof. (* .in *)
Fail elpi refine (H).  (* .fails *)
elpi refine (H _).
Abort.

(*|

--------------------------------
Ltac arguments to Elpi arguments
--------------------------------

It is customary to use the Tactic Notation command to attach a nicer syntax
to Elpi tactics.

In particular `elpi tacname` accepts as arguments the following `bridges
for Ltac values <https://coq.inria.fr/doc/proof-engine/ltac.html#syntactic-values>`_ :

* `ltac_string:(v)` (for `v` of type `string` or `ident`)
* `ltac_int:(v)` (for `v` of type `int` or `integer`)
* `ltac_term:(v)` (for `v` of type `constr` or `open_constr` or `uconstr` or `hyp`)
* `ltac_(string|int|term)_list:(v)` (for `v` of type `list` of ...)

Note that the Ltac type associates some semantics to the action of passing
the arguments. For example `hyp` will accept an identifier only if it is
an hypotheses of the context. While `uconstr` does not type check the term,
which is the recommended way to pass terms to an Elpi tactic (since it is
likely to be typed anyway by the Elpi tactic).
  
|*)

Tactic Notation "use" uconstr(t) :=
  elpi refine ltac_term:(t).

Tactic Notation "use" hyp(t) :=
  elpi refine ltac_term:(t).

Lemma test_use (P Q : Prop) (H : P -> Q) (p : P) : Q.
Proof. (* .in *)
use (H _).
Fail use q.  (* .fails .in .messages *)
use p.
Qed.

Tactic Notation "print" uconstr_list_sep(l, ",") :=
  elpi print_args ltac_term_list:(l).

Lemma test_print (P Q : Prop) (H : P -> Q) (p : P) : Q.
print P, p, (H p). (* .in .messages *)
Abort.

(*|

========
Examples
========

-------------------------------
Let's code `assumption` in Elpi
-------------------------------

`assumption` is a very simple tactic: we look up in the proof
context for an hypothesis which unifies with the goal.
Recall that `Ctx` is made of :builtin:`decl` and :builtin:`def`
(here, for simplicity, we ignore the latter case).

|*)

Elpi Tactic assumption.
Elpi Accumulate lp:{{
  solve (goal Ctx _ Ty _ _ as G) GL :-
    % H is the name for hyp, Ty is the goal
    std.mem Ctx (decl H _ Ty),
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof. (* .in *)
split.
elpi assumption.
Fail elpi assumption.  (* .fails *)
Abort.

(*|

As we hinted before, Elpi's equality is alpha equivalence. In the second
goal the assumption has type `Q` but the goal has type `id Q` which is
convertible (unifiable, for Coq's unification) to `Q`.

Let's improve our tactic looking for an assumption which is unifiable with
the goal, an not just alpha convertible. The :builtin:`coq.unify-leq`
calls Coq's unification for types (on which cumulativity applies, hence the
`-leq` suffix). The :stdlib:`std.mem` utility, thanks to backtracking,
eventually finds an hypothesis that satisfies the following predicate
(ie unifies with the goal).

|*)

Elpi Tactic assumption2.
Elpi Accumulate lp:{{
  solve (goal Ctx _ Ty _ _ as G) GL :-
    % std.mem is backtracking (std.mem! would stop at the first hit)
    std.mem Ctx (decl H _ Ty'), coq.unify-leq Ty' Ty ok,
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption2  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof. (* .in *)
split.
all: elpi assumption2.
Qed.

(*|
 
:libtac:`refine` does unify the type of goal with the type of the term,
hence we can simplify the code further. We obtain a
tactic very similar to our initial `blind` tactic, which picks
candidates from the context rather than from the program itself.

|*)

Elpi Tactic assumption3.
Elpi Accumulate lp:{{
  solve (goal Ctx _ _ _ _ as G) GL :-
    std.mem Ctx (decl H _ _),
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption3  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof. (* .in *)
split.
all: elpi assumption3.
Qed.

(*|

------------------------
Let's code `set` in Elpi
------------------------

The `set` tactic takes a term, possibly with holes, and
makes a let-in out of it.

It gives us the occasion to explain the :lib:`copy` utility.

|*)

Elpi Tactic find.
Elpi Accumulate lp:{{

solve (goal _ _ T _ [trm X]) _ :-
  pi x\
    copy X x => copy T (Tabs x),
    if (occurs x (Tabs x))
       (coq.say "found" {coq.term->string X})
       (coq.ltac.fail _ "not found").
}}.
Elpi Typecheck.

Lemma test_find (P Q : Prop) : (P /\ P) \/ (P /\ Q).
Proof. (* .in *)
elpi find (P).
Fail elpi find (Q /\ _).  (* .fails .in .messages *)
elpi find (P /\ _).
Abort.

(*|

This first approximation only prints the term it found, or better the first
intance of the given term.

Now lets focus on :lib:`copy`. An excerpt:

.. code:: elpi

   copy X X :- name X.     % checks X is a bound variable
   copy (global _ as C) C.
   copy (fun N T F) (fun N T1 F1).
     copy T T1, pi x\ copy (F x) (F1 x).
   copy (app L) (app L1) :- !, std.map L copy L1.

Copy implements the identity: it builds, recursively, a copy of the first
term into the second argument. Unless one loads in the context a new rule,
which takes precedence over the identity ones. Here we load:

.. code:: elpi

    copy X x

which, at run time, looks like

.. code:: elpi

    copy (app [global (indt «andn»), sort prop, sort prop, c0, X0 c0 c1]) c2

and that rule masks the one for :constructor:`app` when the 
sub-term being copied matches `(P /\ _)`. The first time this rule
is used :e:`X0` is assigned, making the rule represent the term `(P /\ P)`.

Now let's refine the tactic to build a let-in, and complain if the
desired name is already taken.

|*)

Elpi Tactic set.
Elpi Accumulate lp:{{

solve (goal _ _ T _ [str ID, trm X] as G) GL :-
  pi x\
    copy X x => copy T (Tabs x),
    if (occurs x (Tabs x))
       (if (coq.ltac.id-free? ID G) true
           (coq.warn ID "is already taken, Elpi will make a name up"),
        coq.id->name ID Name,
        Hole x = {{ _ : lp:{{ Tabs x }} }}, % a hole with a type
        refine (let Name _ X x\ Hole x) G GL)
       (coq.ltac.fail _ "not found").

}}.
Elpi Typecheck.

Lemma test_set (P Q : Prop) : (P /\ P) \/ (P /\ Q).
Proof. (* .in *)
elpi set "x" (P).
unfold x.
Fail elpi set "x" (Q /\ _).  (* .fails .in .messages *)
elpi set "x" (P /\ _).
Abort.

(*|

For more examples of (basic) tactics written in Elpi see the
`eltac app <https://github.com/LPCIC/coq-elpi/tree/master/apps/eltac>`_.


.. _The-proof-engine:

================
The proof engine
================

In this section we dive into the details of the proof engine, that is
how goals are represented in Elpi and how things are wired up behind the scenes.

Let's inspect the proof state a bit deeper:

|*)

Elpi Tactic show_more.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type,
    coq.say "Proof state:",
    coq.sigma.print.

}}.
Elpi Typecheck.

Lemma test_show_more x : x + 1 = 0.
elpi show_more. (* .in .messages *)
Abort.

(*|

In addition to the goal we print the Elpi and Coq proof state,
plus the link between them.
The proof state is the collection of goals together with their types.

On the Elpi side this state is represented by constraints for the :e:`evar`
predicate.

.. mquote:: .s(elpi show_more).msg{*c0*evar (X1 c0)*suspended on X1, X0*}
   :language: text

One can recognize the set of bound variables `{c0}`, the hypothetical
context of rules about these variable (that also corresponds to the proof
context), and finally the suspended goal :e:`evar (X1 c0) .. (X0 c0)`.

The set of constraints on `evar` represents the Coq data structure called
sigma (sometimes also called evd or evar_map) that is used to
represent the proof state in Coq. It is printed just afterwards:
 
.. mquote:: .s(elpi show_more).msg{EVARS:*[?]X56*x + 1 = 0*}
   :language: text

.. mquote:: .s(elpi show_more).msg{Coq-Elpi mapping:*RAW:*[?]X56 <-> *X1*ELAB:*[?]X56 <-> *X0*}
   :language: text

Here `?X56` is a Coq evar linked with Elpi's :e:`X0` and :e:`X1`.
:e:`X1` represents the goal (the trigger) while :e:`X0` represent the proof.
The meaning of the :e:`evar` Elpi predicate linking the two is that the term
assigned to the trigger :e:`X1` has to be elaborated to the final proof term
:e:`X0`, that should be a well typed term of type `x + 1 = 0`.
This means that when an Elpi tactic assigns a value to :e:`X1` some procedure to
turn that value into :e:`X0` is triggered. That procedure is called
elaboration and it is currently implemented by calling the
:builtin:`coq.elaborate-skeleton` API.

Given this set up, it is impossible to use a term of the wrong type as a
Proof. Let's rewrite the `split` tactic without using :libtac:`refine`.

|*)

Elpi Tactic split_ll.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ lp:A /\ lp:B }} Proof []) GL :- !,
    Trigger = {{ conj _ _ }}, % triggers elaboration, filling Proof
    Proof = {{ conj lp:Pa lp:Pb }},
    GL = [seal G1, seal G2],
    G1 = goal Ctx _ A Pa [],
    G2 = goal Ctx _ B Pb [].
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split_ll : exists t : Prop, True /\ True /\ t.
Proof. (* .in *)
eexists.
repeat elpi split_ll.
all: elpi blind.
Qed.

(*|

Crafting by hand the list of subgoal is not easy.
In particular here we did not set up the new trigger for :e:`Pa` and :e:`Pb`,
nor seal the goals appropriately (we did not bind proof variables).

The :builtin:`coq.ltac.collect-goals` API helps us doing this.

|*)

Elpi Tactic split_ll_bis.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ lp:A /\ lp:B }} Proof []) GL :- !,
    % this triggers the elaboration
    Trigger = {{ conj _ _ }},                   
    % we only take main goals
    coq.ltac.collect-goals Proof GL _ShelvedGL.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split_ll_bis : exists t : Prop, True /\ True /\ t.
Proof. (* .in *)
eexists.
repeat elpi split_ll_bis.
all: elpi blind.
Qed.

(*|

At the light of that, :libtac:`refine` is simply:

.. code:: elpi

     refine T (goal _ RawEv _ Ev _) GS :-
       RawEv = T, coq.ltac.collect-goals Ev GS _.

Now that we know the low level plumbing, we can use :libtac:`refine` ;-)

The only detail we still have to explain is what exactly a
:type:`sealed-goal` is. A sealed goal wraps into a single object all
the proof variables and the assumptions about them, making this object easy
(or better, sound) to pass around.

------------------
multi-goal tactics
------------------

Since Coq 8.4 tactics can see more than one goal (multi-goal tactics).
You can access this feature by using `all:` goal selector:

* if the tactic is a regular one, it will be used on each goal independently
* if the tactic is a multi-goal one, it will receive all goals

In Elpi you can implement a multi-goal tactic by providing a rule for
the :builtin:`msolve` predicate. Since such a tactic will need to manipulate
multiple goals, potentially living in different proof context, it receives
a list of :type:`sealed-goal`, a data type which seals a goal and
its proof context.

|*)

Elpi Tactic ngoals.
Elpi Accumulate lp:{{

  msolve GL _ :-
    coq.say "#goals =" {std.length GL},
    coq.say GL.

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) : P /\ Q.
Proof. (* .in *)
split.
all: elpi ngoals.
Abort.

(*|

This simple tactic prints the number of goals it receives, as well as
the list itself. We see something like:

.. mquote:: .s(elpi ngoals).msg{*goals =*}
   :language: text

.. mquote:: .s(elpi ngoals).msg{*nabla*}
   :language: elpi

:constructor:`nabla` binds all proof variables, then :constructor:`seal`
holds a regular goal, which in turn carries the proof context.

In order to operate inside a goal one can use the :libtac:`coq.ltac.open` utility,
which postulates all proof variables using :e:`pi x\ ` and loads the proof
context using :e:`=>`.

Operating on multiple goals at the same time is doable, but not easy.
In particular the two proof context have to be related in some way.
   
The following simple multi goal tactic shrinks the list of goals by
removing duplicates. As one can see, there is much room for improvement
in the :e:`same-ctx` predicate.

|*)

Elpi Tactic undup.
Elpi Accumulate lp:{{

  pred same-goal i:sealed-goal, i:sealed-goal.
  same-goal (nabla G1) (nabla G2) :-
    % TODO: proof variables could be permuted
    pi x\ same-goal (G1 x) (G2 x).
  same-goal (seal (goal Ctx1 _ Ty1 P1 _) as G1)
            (seal (goal Ctx2 _ Ty2 P2 _) as G2) :-
    same-ctx Ctx1 Ctx2,
    % this is an elpi builtin, aka same_term, which does not
    % unify but rather compare two terms without assigning variables
    Ty1 == Ty2,
    P1 = P2.

  pred same-ctx i:goal-ctx, i:goal-ctx.
  same-ctx [] [].
  same-ctx [decl V _ T1|C1] [decl V _ T2|C2] :-
    % TODO: we could compare up to permutation...
    % TODO: we could try to relate def and decl
    T1 == T2,
    same-ctx C1 C2.

  pred undup i:sealed-goal, i:list sealed-goal, o:list sealed-goal.
  undup _ [] [].
  undup G [G1|GN] GN :- same-goal G G1.
  undup G [G1|GN] [G1|GL] :- undup G GN GL.

  msolve [G1|GS] [G1|GL] :-
    % TODO: we could find all duplicates, not just
    % copies of the first goal...
    undup G1 GS GL.

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) (p : P) (q : Q) : P /\ Q /\ P.
Proof. (* .in *)
repeat split.
Show Proof. (* .in .messages *)
all: elpi undup.
Show  Proof. (* .in .messages *)
- apply p.
- apply q.
Qed.

(*|

The two calls to show proof display, respectively:

.. mquote:: .s(Show Proof).msg{*conj [?]Goal (conj [?]Goal0 [?]Goal1)*}
   :language: text

.. mquote:: .s(Show  Proof).msg{*conj [?]Goal (conj [?]Goal0 [?]Goal)*}
   :language: text

the proof term is the same but for the fact that after the tactic the first
and last missing subterm (incomplete proof tree branch) are represented by
the same hole `?Goal0`. Indeed by solving one, we can also solve the other.

-------------
LCF tacticals
-------------

On the notion of sealed-goal it is easy to define the usual LCF combinators,
also known as Ltac tacticals. Tacticals usually take in input one or more
tactic, here the precise type definition:

.. code:: elpi

   typeabbrev tactic (sealed-goal -> (list sealed-goal -> prop)).

A few tacticals can be fond in the
`elpi-ltac.elpi file <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_.
For example this is the code of :libtac:`try`:

.. code:: elpi

   pred try i:tactic, i:sealed-goal, o:list sealed-goal.
   try T G GS :- T G GS.
   try _ G [G].

------------------------------
Setting arguments for a tactic
------------------------------

As we hinted before, tactic arguments are attached to the goal since
they can mention proof variables. So the Ltac code:

.. code:: coq

    intro H; apply H.

has to be seen as 3 steps, starting from a goal `G`:

* introduction of `H`, obtaining `G1`
* setting the argument `H`, obtaining `G2`
* calling apply, obtaining `G3`

|*)

Elpi Tactic argpass.
Elpi Accumulate lp:{{

% this directive lets you use short names
shorten coq.ltac.{ open, thenl, all }.

type intro open-tactic. % goal -> list sealed-goal
intro G GL :- refine {{ fun H => _ }} G GL.

type set-arg-n-hyp int -> open-tactic.
set-arg-n-hyp N (goal Ctx _ _ _ _ as G) [SG1] :-
  std.nth N Ctx (decl X _ _),
  coq.ltac.set-goal-arguments [trm X] G (seal G) SG1.

type apply open-tactic.
apply (goal _ _ _ _ [trm T] as G) GL :- refine T G GL.

msolve SG GL :-
  all (thenl [ open intro,
               open (set-arg-n-hyp 0),
               open apply ]) SG GL.

}}.
Elpi Typecheck.

Lemma test_argpass (P : Prop) : P -> P.
Proof. (* .in *)
elpi argpass.
Qed.

(*|

Of course the tactic playing the role of `intro` could communicate back
a datum to be passed to what follows

.. code:: elpi

     thenl [ open (tac1 Datum), open (tac2 Datum) ]

but the binder structure of :type:`sealed-goal` would prevent :e:`Datum`
to mention proof variables, that would otherwise escape the sealing.

The utility :libtac:`set-goal-arguments`:

.. code:: elpi

     coq.ltac.set-goal-arguments Args G G1 G1wArgs

tries to move :e:`Args` from the context of :e:`G` to the one of :e:`G1`.
Relating the two proof contexts is not obvious: you may need to write your
own procedure if the two contexts are very distant.

================
Tactics in terms
================

Elpi tactics can be used inside terms via the usual `ltac:(...)`
quotation, but can also be exported to the term grammar.

Here we write a simple tactic for default values, which
optionally takes a bound to the search depth.

|*)

Elpi Tactic default.
Elpi Accumulate lp:{{

  pred default i:term, i:int, o:term.

  default _ 0 _ :- coq.ltac.fail _ "max search depth reached".
  default {{ nat }} _ {{ 46 }}.
  default {{ bool }} _ {{ false }}.
  default {{ list lp:A }} Max {{ cons lp:D nil }} :-
    Max' is Max - 1, default A Max' D.

  solve (goal _ _ T _ [] as G) GL :-
    default T 9999 P,
    refine P G GL.

}}.
Elpi Typecheck.
Elpi Export default.

Definition foo : nat := default.
Print foo.

Definition bar : list bool := default.
Print bar.

(*|

The grammar entries for Elpi tactics in terms take an arbitrary
number of arguments with the limitation that they are all terms:
you can't pass a string or an integer as one would normally do.

Here we use Coq's primitive integers to pass the search depth
(in a compact way).

|*)

Elpi Accumulate default lp:{{
  solve (goal _ _ T _ [trm (primitive (uint63 Max))] as G) GL :-
    coq.uint63->int Max MaxI,    
    default T MaxI P,
    refine P G GL.
}}.
Elpi Typecheck.

From Coq Require Import  Uint63.
Open Scope uint63_scope.

Fail Definition baz : list nat := default 1.  (* .fails *)

Definition baz : list nat := default 2.
Print baz.

(*|

That is all folks!

|*)
