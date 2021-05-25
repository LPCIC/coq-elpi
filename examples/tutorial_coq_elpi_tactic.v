From elpi Require Import elpi.
(**
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
*)

(** ----------------------- ----------------------- -----------------------

   This tutorial focuses on the implementation of Coq tactics.

   This tutorial assumes the reader is familiar with Elpi and the HOAS
   representation of Coq terms; if it is not the case, please take a look at
   this other tutorials first:
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_elpi_lang.v
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_coq_elpi_HOAS.v

   - Defining tactics
   - Example: Synthesizing a term

*)


(**
   In Coq a proof is just a term, and an incomplete proof is just a term
   with holes standing for the open goals.

  When a proof starts there is just one hole (one goal) and its type
  is the statement one wants to prove. Then proof construction makes
  progress by instantiation: a term possibly containing holes is
  grafted to the hole corresponding to the current goal. What a tactic
  does behind the scenes is to synthesize this partial term.

  While the entry point for commands is "main" then one for tactics
  is called "solve". Tactics written in Elpi can be invoked via the
  "elpi" tactic.

  Let's define a simple tactic that prints the current goal.
*)

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type,
    coq.say "Proof state:",
    coq.sigma.print.

}}.
Elpi Typecheck.

Lemma tutorial x y  : x + 1 = y.
Proof.
elpi show.
Abort.

(**

  In the Elpi code up there "Proof" is the hole for the current goal,
  "Type" the statement to be proved and "Ctx" the proof context. Since we
  don't assign "Proof" the tactic makes no progess. Elpi prints something
  like this:

   [decl c0 `x` (global (indt «nat»)), decl c1 `y` (global (indt «nat»))] 
   |- X0 c0 c1 : 
     app
      [global (indt «eq»), global (indt «nat»), 
       app
        [global (const «Nat.add»), c0, 
         app [global (indc «S»), global (indc «O»)]], c1]

  The first line is the proof context, and is a list of variables declarations.
  Proof variables are bound Elpi variables (here "c0" and "c1"), the context is
  a list of predicates holding on them. For example

    decl c0 `x` (global (indt «nat»))

  asserts that "c0" (pretty printed as "`x`") has type "nat".

  Then we see that the value of "Proof" is "X0 c0 c1". This means that the
  proof of the current goal is represented by Elpi's variable "X0" and that
  the variable has "c0" and "c1" in scope (the proof can use them).

  Finally we see find the type of the goal "x + 1 = y".

  After that Elpi prints the proof state. The proof state is the collection of
  goals together with their types. In the side of Elpi this state is represented
  by constraints for the "evar" predicate.

   {c0 c1} :
   decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
   ?- evar (X0 c0 c1) 
       (app
         [global (indt «eq»), global (indt «nat»), 
          app
           [global (const «Nat.add»), c0, 
            app [global (indc «S»), global (indc «O»)]], c1]) (X1 c0 c1)  /* suspended on X0, X1 */

  One can recognize the set of bound variables "{c0 c1}", the hypothetical
  context of clauses about them (that also corresponds to the proof context),
  and finally the suspended query "evar (X0 c0 c1) .. (X1 c0 c1)".

  The set of constraints on "evar" represents the Coq data structure called
  "sigma" (hence the name of the built-in to print it) that is used to
  represent the proof state in Coq. It is printed just afterwards:

   ...
   sigma =
    EVARS:
     ?X16==[x y |- x + 1 = y] (goal evar) {?Goal}
   ...
   Coq-Elpi mapping:
     ?X16 <-> X1

  The last part is a bijection between Coq's existential variables (AKA evars)
  and Elpi's unification variables. Coq uses the evar ?X16 in the example above
  to represent the (missing) proof of the goal. On the Elpi side X1 plays that
  role.

  One last thing to explain is why in Elpi the variable used to represent the
  goal is X0 while the one to represent the proof is X1. The meaning of the
  "evar" Elpi predicate linking the two is that the term assigned to the
  former has to be elaborated to the latter, that is the actual proof of the
  goal, when read back in Coq, should be a well typed term. This means that
  when an Elpi tactic  assigns a value to X0 some procedure to turn that
  value into X1 is resumed. That procedure is called elaborator. A possible
  implementation is via the coq.typecheck built-in. An alternative one is
  the "of" predicate implemented in
  https://github.com/LPCIC/coq-elpi/blob/master/engine/coq-elaborator.elpi

  Given this set up, it is impossible to use a term of the wrong type as a
  proof.
*)

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve (goal _ Proof _ _ _) _ :- Proof = {{0}}.
  solve (goal _ Proof _ _ _) _ :- Proof = {{I}}.
}}.
Elpi Typecheck.

Lemma tutorial : True * nat.
Proof.
split.
- elpi blind.
- elpi blind.
Qed.

(**
   Elpi's equality on ground (evar free) Coq terms corresponds to
   alpha equivalence.
   Moreover the head of a clause for the solve predicate is matched against the
   goal: this operation cannot assign unification variables
   in the goal, only variables in the clause's head. As a consequence
   the following clause for "solve" only triggers when the statement
   features an explicit conjunction.
*)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal _ RawProof {{ lp:A /\ lp:B }} Proof _) GL :- !,
    RawProof = {{ conj _ _ }},
    coq.ltac.collect-goals Proof GL _ShelvedGL,
    GL = [seal G1, seal G2],
    G1 = goal _ _ A _ _,
    G2 = goal _ _ B _ _.
  solve _ _ :-
    % This signals a failure in the Ltac model. A failure in Elpi, that
    % is no more cluases to try, is a fatal error that cannot be catch
    % by Ltac combinators like repeat.
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma fast_path : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split.
all: elpi blind.
Show Proof.
Qed.

(**
   Remark: in the third case the type checking constraint
   on Proof succeeds, i.e. "of" internally unifies the type of the given term
   with the goal. In this case instantiating the statement of the goal to
   "nat" fails because "t" is a "Prop", so it picks "I".

   Remark: The last argument of "solve" is the list of subgoals, here we
   build its value "GL" by hand. Library functions in ltac.elpi, namely
   collect-goals and refine, can do this job for you.
*)

(**
    Let's implement Ltac's "match goal with ... end".

    It is easy to implement it in Elpi since it is made of two components:
    - a first order matching procedure (no unfolding)
    - non-determinism to "pair" hypotheses and patterns for the context.

    The first ingredient is the standard "copy" predicate.
    The second ingredient is the composition of the forall and exists
      standard list "iterators".

*)

Elpi Tactic tutorial_ltac.
Elpi Accumulate lp:{{

kind goal-pattern type.
type with goal-ctx -> term -> prop -> goal-pattern.
pred pattern-match i:goal, o:goal-pattern.
pred pmatch i:term, o:term.
pred pmatch-hyp i:prop, o:prop.

:name "pmatch:syntactic"
pmatch T P :- copy T P.

% If one asks for a decl, we also find a def
pmatch-hyp (decl X N Ty)    (decl X N PTy) :- pmatch Ty PTy.
pmatch-hyp (def X N Ty _) (decl X N PTy) :- pmatch Ty PTy.
pmatch-hyp (def X N Ty B) (def X N PTy PB) :- pmatch B PB, pmatch Ty PTy.

% We first match the goal, then we see if for each hypothesis pattern
% there exists a context entry that matches it, finally we test the condition.
pattern-match (goal Hyps _ Type _ _) (with PHyps PGoal Cond) :-
  pmatch Type PGoal,
  (std.forall PHyps p\ std.exists Hyps h\ pmatch-hyp h p),
  Cond.

solve (goal _ E _ _ _ as G) [] :-
  pattern-match G (with [decl X NameX T,decl Y NameY T] T (not(X = Y))),
  coq.say "Both" NameX "and" NameY "solve the goal, picking the first one",
  E = X.

}}.
Elpi Typecheck.

Lemma ltac1 (x y : bool) (H : x = y) (H0 : y = y) (H1 := H) (H2 : x = x) : x = y.
Proof.
elpi tutorial_ltac.
Qed.

(** Let's now extract higher order terms from the context, like the
   predicate about "y" *)

Elpi Accumulate lp:{{

pred context-of i:term, i:term, o:(term -> term).
context-of What Where F :- pi x\ (copy What x) => copy Where (F x).

pred constant? i:(A -> B).
constant? F :- pi x y\ F x = F y.

solve G GS :-
  pattern-match G (with [decl _X _NameX Ty] T (context-of T Ty C, not(constant? C))),
  refine {{let ctx := fun y => lp:(C y) in lp:(Ng_ ctx) }} G GS.
}}.
Elpi Typecheck.

Lemma ltac2 x (H : exists y, x <> 0 /\ y = x) : x <> 0 .
Proof.
elpi tutorial_ltac.
change (ctx (x<>0)) in H.
Abort.
