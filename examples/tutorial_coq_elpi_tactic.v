(*|

Tutorial on Coq tactics
***********************

:author: Enrico Tassi

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

* APIs (eg `coq.say`) and data types (eg Coq terms) are loaded from
  `coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi>`_
* some utilities, like `copy` or `whd1` are loaded from
  `elpi-tactic-template.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi>`_
  
  
The second one `Elpi Accumulate ...` loads some extra code.
The `Elpi Accumulate ...` family of commands lets one accumulate code
taken from:

* verbatim text `Elpi Accumulate lp:{{ <code> }}`
* source files `Elpi Accumulate File <path>`
* data bases (Db) `Elpi Accumulate Db <name>`

Accumulating code via inline text or file is equivalent, the AST of <code>
is stored in the .vo file (the external file does not need to be installed).
We invite the reader to look up the description of data bases in the tutorial
about commands.
  
Once all the code is accumulated `Elpi Typecheck` verifies that the
code does not contain the most frequent kind of mistakes. This command
considers some mistakes minor and only warns about them. You can
pass `-w +elpi.typecheck` to `coqc` to turn these warnings into errors.
  
The entry point for tactics is called `solve` which maps a `goal`
into a list of `sealed-goal` (representing subgoals).
  
Tactics written in Elpi can be invoked by prefixing its name with `elpi`.

|*)

Lemma tutorial x y  : x + 1 = y.
elpi show.
Abort.

(*|

In the Elpi code up there `Proof` is the hole for the current goal,
`Type` the statement to be proved and `Ctx` the proof context (the list of
hypotheses). Since we don't assign `Proof` the tactic makes no progess.
Elpi prints somethinglike this:

.. code::

    Goal:
    [decl c0 `x` (global (indt «nat»)), decl c1 `y` (global (indt «nat»))] 
    |- X0 c0 c1 : 
       app [global (indt «eq»), global (indt «nat»), 
            app [global (const «Nat.add»),
                 c0, app [global (indc «S»), global (indc «O»)]],
            c1]

The first line is the proof context:
proof variables are bound Elpi variables (here `c0` and `c1`), the context is
a list of predicates holding on them (their type in Coq). For example:

.. code::

    decl c0 `x` (global (indt «nat»))

asserts that `c0` (pretty printed as `x`) has type `nat`.

Then we see that the value of `Proof` is `X0 c0 c1`. This means that the
proof of the current goal is represented by Elpi's variable `X0` and that
the variable has `c0` and `c1` in scope (the proof term can use them).

Finally we see the type of the goal `x + 1 = y`.

The `_Trigger` component, which we did not print, is a variable that, when
assigned, trigger the elaboration of its value against the type of the goal
and obtains a value for `Proof` this way.

Keeping in mind that the solve predicate relates one goal to a list of
subgoals, we implement our first tactic which blindly tries to solve the goal.

|*)

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{0}}.
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{I}}.
}}.
Elpi Typecheck.

Lemma test_blind : True * nat.
Proof.
split.
- elpi blind.
- elpi blind.
Show Proof.
Qed.

(*|

Since the assignment of a term to `Trigger` triggers its elaboration against
the expected type (the goal statement), assigning the wrong proof term
results in a failure which in turn results in the other clause being tried.

Assigning `Proof` directly is "unsound" in the sense that no automatic check
is performed.

|*)

Elpi Tactic blind_bad.
Elpi Accumulate lp:{{
  solve (goal _ _ _ Proof _) [] :- Proof = {{0}}.
  solve (goal _ _ _ Proof _) [] :- Proof = {{I}}.
}}.
Elpi Typecheck.

Lemma test_blind_bad : True * nat.
Proof.
split.
- elpi blind_bad.
- elpi blind_bad.
Show Proof.
Fail Qed.
Abort.


(*|

For now, this is all about the low level mechanics of tactics which is
developed further in the section `The-proof-engine`_.

We now focus on how to better integrate tactics written in Elpi with Ltac.

For a simple tactic like blind the list of subgoals is easy to write, since
it is empty, but in general one should collect all the holes in
the value of Proof (the checked proof term) and build goals out of them.

There is a family of APIs named after `refine`, the mother of all tactics, in
`elpi-ltac.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_
which does this job for you.

Usually a tactic builds a (possibly partial) term and calls `refine` on it.

Let's rewrite the `blind` tactic using this schema.

|*)


Elpi Tactic blind2.
Elpi Accumulate lp:{{
  solve G GL :- refine {{0}} G GL.
  solve G GL :- refine {{I}} G GL.
}}.
Elpi Typecheck.

Lemma test_blind2 : True * nat.
Proof.
split.
- elpi blind2.
- elpi blind2.
Qed.

(*|

This schema works even if the term is partial, that is if it contains holes
corresponding to missing sub proofs. Let's write a tactic which opens
a few subgoals, let's implement the `split` tactic.

.. important::

   Elpi's equality (that is, unification) on Coq terms corresponds to
   alpha equivalence, we can use that to make our tactic less blind.

The head of a clause for the solve predicate is matched against the
goal. This operation cannot assign unification variables in the goal, only
variables in the clause's head.
As a consequence the following clause for `solve` only triggers when
the statement features an explicit conjunction.

|*)

About conj. (* conj : forall [A B : Prop], A -> B -> A /\ B *)

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
Proof.
eexists.
repeat elpi split. (* The failure is catched by Ltac's repeat *)
(* Remark that the last goal is left untouched, since
   it did not match the pattern {{ _ /\ _ }}. *)
all: elpi blind.
Show Proof.
Qed.

(*|

The tactic `split` succeeds twice, stopping on the two identical goals `True` and
the one which is an evar of type `Prop`.

We then invoke `blind` on all goals. In the third case the type checking
constraint triggered by assigning `{{0}`} to `Proof` fails because
its type `{{nat}}` is not of sort `Prop`, so it backtracks and picks `{{I}}`.

Another common way to build an Elpi tactic is to synthesize a term and
then call some Ltac piece of code finishing the work.

`coq.ltac.call` invokes an Ltac piece of code passing to it the desired
arguments. Then it builds the list of subgoals.

Here we pass an integer, passed to fail, and a term, passed to apply.

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
Proof.
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

Lemma test_print_args : True.
elpi print_args 1 x "a b" (1 = 0).
Abort.

(*|

The convention is that numbers like `1` are passed a `int <arg>`,
identifiers or strings are passed as `str <arg>` and terms
have to be put between parentheses. 

Remark that terms are received in raw format, eg before elaboration.
Indeed the type argument to `eq` is a variable.
One can use APIs like `coq.elaborate-skeleton` to infer holes like `X0`.

See the `argument` data type in 
`coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi>`_.
for a detailed decription of all the arguments a tactic can receive.

Now let's write a tactic which behave pretty much like the `refine` one
from Coq, but prints what it does.

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
Proof.
Fail elpi refine (H).
elpi refine (H _).
Abort.

(*|

It is customary to use the Tactic Notation command to attach a nicer syntax
to Elpi tactics.

In particular elpi tacname accepts as arguments the following bridges
for Ltac:

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

(*|

============================
Examples: assumption and set
============================

A very simple tactic we can implement is assumption: we look up in the proof
context for an hypothesis which unifies with the goal.
Recall that Ctx is made of decl and def clauses (here, for simplicity, we
ignore the latter case).

|*)

Elpi Tactic assumption.
Elpi Accumulate lp:{{
  solve (goal Ctx _ Ty _ _ as G) GL :-
    % H is the name of hyp, Ty is the goal
    std.mem Ctx (decl H _ Ty),
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof.
split.
elpi assumption.
Fail elpi assumption.
Abort.

(*|

As we hinted before, Elpi's equality is alpha equivalence. In the second
goal the assumption has type `Q` but the goal has type `id Q` which is
convertible (unifiable, for Coq's unification) to `Q`.

Let's improve out tactic looking for an assumption which is unifiable with
the goal, an not just alpha convertible

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
Proof.
split.
all: elpi assumption2.
Qed.

(*|
 
`refine` does unify the type of goal with the type of the term, hence we can
just write the follwing code, which is very close to our initial `blind`
tactic, but it picks candidates from the context.

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
Proof.
split.
all: elpi assumption3.
Qed.

(*|

Now let's write a tactic which takes a term, possibly with holes, and
makes a let-int out of it, a bit like the `set` tactic.

It will be the occasion to explain the `copy` utility.

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

Lemma test_find (P Q : Prop) : P /\ P.
Proof.
elpi find (P).
Fail elpi find (Q).
elpi find (P /\ _).
Abort.

(*|

This first approximation only prints the term it found, or better the first
intance of the given term.

Now lets focus on `copy`. The standard
Coq library `coq-lib.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/coq-lib.elpi>`_.
(loaded by the command template) contains a definition of copy
for terms and declarations. An excerpt:

.. code::

    copy X X :- name X.
    copy (global _ as C) C.
    copy (fun N T F) (fun N T1 F1).
      copy T T1, pi x\ copy (F x) (F1 x).
    copy (app L) (app L1) :- !, std.map L copy L1.

Copy implements the identity: it builds, recursively, a copy of the first
term into the second argument. Unless one loads in the context a new clause,
which takes precedence over the identity ones. Here we load

.. code::

    copy X x

which, at run time, looks like

.. code::

    copy (app [global (indt «andn»), sort prop, sort prop, c0, X0 c0 c1]) c2

and that clause masks the one for `app` when the sub-term being copied is
matches `(P /\ _)`.

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

Lemma test_set (P Q : Prop) : P /\ P.
Proof.
elpi set "x" (P).
unfold x.
Fail elpi set "x" (Q).
elpi set "x" (P /\ _).
Abort.

(*|

The new hole is annotated with a type. Here we use quotations to write
that term, but we could have used the commodity macro

.. code::
  
   @cast (Hole x) (Tabs x)

which unfolds to

.. code::

  let _ (Tabs x) (Hole x) y\y

which is how "type casts" are represented in the HOAS of terms.

For more example of (basic) tactics written in Elpi see the
`eltac app <https://github.com/LPCIC/coq-elpi/tree/master/apps/eltac>`_.


.. _The-proof-engine:

================
The proof engine
================

In this section we dive into the details of the proof engine, that is
how goals are represented in Elpi and things are wired up behind the scenes.

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
elpi show_more.
Abort.

(*|

In addition to the goal we print the Elpi and Coq proof state,
plus the link between them.
The proof engine is the collection of goals together with their types.

In the side of Elpi this state is represented by constraints for the "evar"
predicate.

One can recognize the set of bound variables `{c0}`, the hypothetical
context of clauses about these variable (that also corresponds to the proof
context), and finally the suspended goal `evar (X1 c0) .. (X0 c0)`.

The set of constraints on `evar` represents the Coq data structure called
sigma (hence the name of the API to print it) that is used to
represent the proof state in Coq. It is printed just afterwards:
 
.. code::

    EVARS:
     ?X56==[x |- x + 1 = 0] (goal evar) {?Goal}

    Coq-Elpi mapping:
    RAW:
    ?X56 <-> X1
    ELAB:
    ?X56 <-> X0

Here `?X56` is a Coq evar linked with Elpi's `X0` and `X1`.
`X1` represents the goal (the trigger) while `X0` represent the proof.
The meaning of the `evar` Elpi predicate linking the two is that the term
assigned to the trigger `X1` has to be elaborated to the final proof term `X0`,
that should be a well typed term of type `x + 1 = 0`.
This means that when an Elpi tactic assigns a value to `X1` some procedure to
turn that value into `X0` is triggered. That procedure is called elaboration and
it is currently implemented by calling the `coq.elaborate-skeleton` API.

Given this set up, it is impossible to use a term of the wrong type as a
proof. Lets declare simle tactic that tries `0` and `I` as proof terms for a
goal, without even looking at it.

The refine utility simply assigns the trigger and then calls the
`coq.ltac.collect-goals` API on the elaborated proof term to get the list
of sub goals

Let's rewrite the split tactic using only low level operations.

|*)

Elpi Tactic split_ll.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ lp:A /\ lp:B }} Proof []) GL :- !,
    Trigger = {{ conj _ _ }},
    Proof = {{ conj lp:Pa lp:Pb }},
    GL = [seal G1, seal G2],
    G1 = goal Ctx _ A Pa [],
    G2 = goal Ctx _ B Pb [].
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split_ll : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split_ll.
all: elpi blind.
Qed.

(*|

Crafting by hand the list of subgoal is not easy.
In particular here we did not set up the new trigger for `Pa` and `Pb`, nor
seal the goals appropriately.

The `coq.ltac.collect-goals` API helps us to do this operation.

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
Proof.
eexists.
repeat elpi split_ll_bis.
all: elpi blind.
Qed.

(*|

At the light of that, refine is simply:

.. code::

     refine T (goal _ RawEv _ Ev _) GS :-
       RawEv = T, coq.ltac.collect-goals Ev GS _.

Now that we know the low level plumbing, we can use `refine`. The only detail
we still have to explain is what exactly a `sealed-goal` is. A sealed goal
wraps into a single object all the proof variable and the assumptions about
them, making this object easy (or better, sound) to pass around. More details
in the next section.

=============================
msolve and tactic composition
=============================

Since Coq 8.4 tactics can see more than one goal (multi-goal tactics).
You can access this feature by using `all: tactic`:

* if the tactic is a regular one, it will be used on each goal independently
* if the tactic is a multi-goal one, it will receive all goals

In Elpi you can implement a multi-goal tactic by providing a clause for
the `msolve` predicate. Since such tactic will need to manipulate multiple
goals, potentially living in different proof context, it receives a list
of sealed-goal, a data type which seals a goal and its proof context.

|*)

Elpi Tactic ngoals.
Elpi Accumulate lp:{{

  msolve GL _ :-
    coq.say "#goals =" {std.length GL},
    coq.say GL.

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) : P /\ Q.
Proof.
split.
all: elpi ngoals.
Abort.

(*|

This simple tactic prints the number of goals it receives, as well as
the list itself. We see something like:

.. code::

   #goals = 2
   [(nabla c0 \
      nabla c1 \
   	   seal
        (goal [decl c1 `Q` (sort prop), decl c0 `P` (sort prop)] (X0 c0 c1) c0 
          (X1 c0 c1) [])), 
    (nabla c0 \
      nabla c1 \
       seal
        (goal [decl c1 `Q` (sort prop), decl c0 `P` (sort prop)] (X2 c0 c1) c1 
          (X3 c0 c1) []))]
   
`nabla` binds all proof variables, then `seal` holds a regular goal, which in
turn carries the context (the type of the proof variables).

In order to operate inside a goal one can use the `coq.ltac.open` utility,
which postulates all proof variables using pi and loads the goal context
using `=>`.

Operating on multiple goals is doable, but not easy. In particular the
two proof context have to be related in some way.
   
The following simple
multi goal tactic shrinks the list of goals by removing duplicates.

|*)

Elpi Tactic undup.
Elpi Accumulate lp:{{

  pred same-goal i:sealed-goal, i:sealed-goal.
  same-goal (nabla G1) (nabla G2) :-
    pi x\ same-goal (G1 x) (G2 x).
  same-goal (seal (goal Ctx1 _ Ty1 P1 _) as G1)
            (seal (goal Ctx2 _ Ty2 P2 _) as G2) :-
    same-ctx Ctx1 Ctx2,
    % this is an elpi builtin, does not unify, just compare
    Ty1 == Ty2,
    P1 = P2.

  pred same-ctx i:goal-ctx, i:goal-ctx.
  same-ctx [] [].
  same-ctx [decl V _ T1|C1] [decl V _ T2|C2] :-
    % TODO: we could compare up to permutation...
    T1 == T2,
    same-ctx C1 C2.

  pred undup i:sealed-goal, i:list sealed-goal, o:list sealed-goal.
  undup _ [] [].
  undup G [G1|GN] GN :- same-goal G G1.
  undup G [G1|GN] [G1|GL] :- undup G GN GL.

  msolve [G1|GS] [G1|GL] :-
    % TODO: we could find all duplicates, not just
    % copies of the first one...
    undup G1 GS GL.

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) (p : P) (q : Q) : P /\ Q /\ P.
Proof.
repeat split.
Show Proof.
all: elpi undup.
Show Proof.
- apply p.
- apply q.
Qed.

(*|

The two calls to show proof display, respectively:

.. code:: coq

    (fun (P Q : Prop) (p : P) (q : Q) => conj ?Goal (conj ?Goal0 ?Goal1))
    (fun (P Q : Prop) (p : P) (q : Q) => conj ?Goal0 (conj ?Goal ?Goal0))

the proof term is the same but for the fact that after the tactic the first
and last missing subterm (incomplete proof tree branch) are represented by
the same hole. Indeed by solving one, we can also solve the other.

On the notion of sealed-goal it is easy to define the usual LCF combinators,
also known as Ltac tacticals. A few ones can be find in the
`elpi-ltac.elpi file <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_.

As we hinted before, tactic arguments are attached to the goal, since
they can mention proof variables. So the Ltac code

.. code:: coq

    intro H; apply H.

has to be seen as 3 steps, starting from a goal G:

* introduction of `H`, obtaining G1
* setting the argument `H`, obtaining G2
* calling apply, obtaining G3

|*)

Elpi Tactic argpass.
Elpi Accumulate lp:{{

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
Proof.
elpi argpass.
Qed.

(*|

Of course the tactic playing the role of `intro` could communicate back
a datum to be passed to what follows

.. code::

     thenl [ open (tac1 Datum), open (tac2 Datum) ]

but the binder structure of `sealed-goal` would prevent `Datum` to mention
proof variables, that would otherwise escape the sealing. The utility

.. code::

     coq.ltac.set-goal-arguments Args G G1 G1wArgs

tries to move `Args` from the context of G to the one of G1. Relating the
two proof contexts is not obvious: you may need to write your own procedure
if the two contexts are very distant.

===============
Tactic in terms
===============

Elpi tactics can be used inside terms via the usual `ltac:(...)`
quotation, but can also be exported in the term grammar.

Here we write a simple tactic for default values, which
optionally takes a bound to the search depth.

|*)

Elpi Tactic default.
Elpi Accumulate lp:{{

  pred default i:term, i:int, o:term.
  default _ 0 _ :- coq.error "max search depth reached".
  default {{nat}} _ {{46}}.
  default {{bool}} _ {{false}}.
  default {{list lp:A}} Max {{cons lp:D nil}} :-
    Max' is Max - 1, default A Max' D.

  solve (goal _ _ T _ [] as G) GL :-
    default T 9999 P,
    refine P G GL.

}}.
Elpi Typecheck.
Elpi Export default.

Definition foo : nat := default.
Definition bar : list bool := default.
Print foo.
Print bar.

(*|

The grammar entries for Elpi tactics in terms take an arbitrary
number of arguments with the limitation that they are all terms:
you can't pass a string or an integer as would normally do.

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

From Coq Require Import  Int63.
Open Scope int63_scope.
Fail Definition baz : list nat := default 1.
     Definition baz : list nat := default 2.
Print baz.

(*|

That is all folks!

.. include:: tutorial_style.rst

|*)
