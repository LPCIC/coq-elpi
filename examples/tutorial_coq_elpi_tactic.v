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
   - Arguments
   - Example: match-goal-with
   - msolve and tactic composition
   - Tactic notations
   - Tactic in terms

*)

(** ------------------------- Defining tactics ---------------------------- *)

(**
   In Coq a proof is just a term, and an incomplete proof is just a term
   with holes standing for the open goals.

  When a proof starts there is just one hole (one goal) and its type
  is the statement one wants to prove. Then proof construction makes
  progress by instantiation: a term possibly containing holes is
  grafted to the hole corresponding to the current goal. What a tactic
  does behind the scenes is to synthesize this partial term.

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

(*

  The tactic declaration is made of 3 parts.
     
  The first one "Elpi Tactic show." sets the current program to hello.
  Since it is declared as a "Tactic" some code is loaded automatically:
  - built-in predicates (eg "coq.say") and data types (eg Coq terms)
    https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
  - some utilities, like "copy" or "whd1"
    https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi
  
  
  The second one "Elpi Accumulate ..." loads some extra code.
  The "Elpi Accumulate ..." family of commands lets one accumulate code
  taken from:
  - verbatim text "Elpi Accumulate lp:{{ <code> }}"
  - source files "Elpi Accumulate File <path>"
  - data bases (Db) "Elpi Accumulate Db <name>"
  Accumulating code via inline text of file is equivalent, the AST of code
  is stored in the .vo file (the external file does not need to be installed).
  We postpone the description of data bases to a dedicated section.
  
  Once all the code is accumulated "Elpi Typecheck" verifies that the
  code does not contain the most frequent kind of mistakes. This command
  considers some mistakes minor and only warns about them. You can
  pass "-w +elpi.typecheck" to coqc to turn these warnings into errors.
  
  The entry point for tactics is called "solve" which maps a goal
  into a list of sealed-goal (representing subgoals).
  
  Tactics written in Elpi can be invoked via the "elpi" tactic.
*)

Lemma tutorial x y  : x + 1 = y.
Proof.
elpi show.
Abort.

(**

  In the Elpi code up there "Proof" is the hole for the current goal,
  "Type" the statement to be proved and "Ctx" the proof context. Since we
  don't assign "Proof" the tactic makes no progess. Elpi prints something
  like this:

    Goal:
    [decl c0 `x` (global (indt «nat»)), decl c1 `y` (global (indt «nat»))] 
    |- X0 c0 c1 : 
       app [global (indt «eq»), global (indt «nat»), 
            app [global (const «Nat.add»),
                 c0, app [global (indc «S»), global (indc «O»)]],
            c1]

  The first line is the proof context:
  proof variables are bound Elpi variables (here "c0" and "c1"), the context is
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
          app [global (const «Nat.add»),
               c0, app [global (indc «S»), global (indc «O»)]],
          c1]) (X1 c0 c1)
      /* suspended on X0, X1 */

  One can recognize the set of bound variables "{c0 c1}", the hypothetical
  context of clauses about these variable (that also corresponds to the proof
  context), and finally the suspended goal "evar (X0 c0 c1) .. (X1 c0 c1)".

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
  value into X1 is triggered.
  That procedure is called elaboration and it is currently implemented by
  calling the coq.elaborate-skeleton built-in.

  Given this set up, it is impossible to use a term of the wrong type as a
  proof. Lets declare simle tactic that tries 0 and I as proof terms for a goal,
  without even looking at it.

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

   Since the assignment of a term to Proof triggers its elaboration against
   the expected type (the goal statement), assigning the wrong proof term
   results in a failure which in turn results in the other clause being tried.

   Elpi's equality on ground (evar free) Coq terms corresponds to
   alpha equivalence.
   Moreover the head of a clause for the solve predicate is matched against the
   goal: this operation cannot assign unification variables in the goal, only
   variables in the clause's head.
   
   As a consequence the following clause for "solve" only triggers when
   the statement features an explicit conjunction.
*)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal _ RawProof {{ lp:A /\ lp:B }} Proof _) GL :- !,
    RawProof = {{ conj _ _ }},                  % this triggers the elaboration
    coq.ltac.collect-goals Proof GL _ShelvedGL, % Proof contains the elaborated
    GL = [seal G1, seal G2],                    % we assert we have 2 subgoals
    G1 = goal _ _ A _ _,                        % one for A
    G2 = goal _ _ B _ _.                        % one for B in this order
  solve _ _ :-
    % This signals a failure in the Ltac model. A failure in Elpi, that
    % is no more cluases to try, is a fatal error that cannot be catch
    % by Ltac combinators like repeat.
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split.
all: elpi blind.
Show Proof.
Qed.

(**
   The tactic eplit succeeds twice, stopping on the two identical goals True and
   the one which is an evar of type Prop.

   We then invoke blind on all goals. In the third case the type checking
   constraint triggered by assigning {{0}} to Proof fails because
   its type {{nat}} is not of sort Prop, so it backtracks and picks {{I}}.

   The last argument of "solve" is the list of subgoals, here we
   use the coq.ltac.collect-goals built-in to build it. The exact meaning of
   sealed-goal and the seal constructor is explained later on, in the section
   about tactic composition.

   This tactic was built, on purpose, using low level primitives.
   The orthodox way to build a tactic is to end it by calling refine
   or coq.ltac.call from
    https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi

   Lets rewrite split using refine
*)

Elpi Tactic split2.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    refine {{ conj _ _ }} G GL.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split2 : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split2.
all: elpi blind.
Show Proof.
Qed.

(*
    So refine, behind the scenes, assigns the trigger and collects the new
    goals. It comes in 3 variants, the regular one we just used, one in which
    the term is not elaborated but just typechecked and a last one
    where the term is not type checked at all (to be used with care, when
    performance is critical).

    coq.ltac.call lets one invoke ltac code, for example

*)

Ltac helper_split3 t := apply t.

Elpi Tactic split3.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    coq.ltac.call "helper_split3" [trm {{ conj }}] G GL.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split3 : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split3.
all: elpi blind.
Show Proof.
Qed.

(** -------------------------- Arguments --------------------------------- *)


Elpi Tactic refine.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [trm T] as G) GL :- !,
    std.assert-ok! (coq.typecheck T Ty) "illtyped",
    coq.say "Using" {coq.term->string T} "of type" {coq.term->string Ty} "in" G,
    refine T G GL.
  solve _ _ :-
    coq.ltac.fail _ "does not apply".
}}.
Elpi Typecheck.

Lemma test_refine (P Q : Prop) (H : P -> Q) : Q.
Proof.
elpi refine (H _).
Abort.

Lemma test_refine (P Q : Prop) : (P -> P) /\ (Q -> Q).
Proof.
split; intros H.
all: elpi refine (H).
Abort.

(** -------------------- Example: match-goal-with -------------------------- *)

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

Elpi Tactic set.
Elpi Accumulate lp:{{

solve (goal _ _ T _ [str ID, trm X] as G) GL :-
  pi x\
    copy X x => copy T (Tabs x),
    if (occurs x (Tabs x))
       (coq.id->name ID Name,
        refine (let Name _ X x\ @cast _ (Tabs x)) G GL)
       (coq.ltac.fail _ "not found").

}}.
Elpi Typecheck.

Lemma test_set (P Q : Prop) : P /\ P.
Proof.
elpi set "x" (P).
unfold x.
Fail elpi set "y" (Q).
elpi set "y" (P /\ _).
Abort.

(** -------------------- msolve and tactic composition --------------------- *)

Elpi Tactic ngoals.
Elpi Accumulate lp:{{

  msolve GL _ :-
    coq.say "#goals =" {std.length GL},
    coq.say GL.

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) (p : P) (q : Q) : P /\ Q /\ P.
Proof.
repeat split.
all: elpi ngoals.
Abort.

.......

Elpi Tactic undup.
Elpi Accumulate lp:{{

  pred same-goal i:sealed-goal, i:sealed-goal.
  same-goal (nabla G1) (nabla G2) :- pi x\ same-goal (G1 x) (G2 x).
  same-goal (seal (goal Ctx1 _ Ty1 P1 _) as G1) (seal (goal Ctx2 _ Ty2 P2 _) as G2) :-
    same-ctx Ctx1 Ctx2,
    Ty1 == Ty2, % this is an elpi builtin, does not unify, just compare
    P1 = P2.

  pred same-ctx i:goal-ctx, i:goal-ctx.
  same-ctx [] [].
  same-ctx [decl V _ T1|C1] [decl V _ T2|C2] :- % we could compare up to permutation...
    T1 == T2,
    same-ctx C1 C2.

  pred undup i:sealed-goal, i:list sealed-goal, o:list sealed-goal.
  undup _ [] [].
  undup G [G1|GN] GN :- same-goal G G1.
  undup G [G1|GN] [G1|GL] :- undup G GN GL.

  msolve [G1|GS] [G1|GL] :-
    undup G1 GS GL. % we could find all duplicates...

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

(* TODO: compose via tactical and set-args *)

(** -------------------- Tactic notations --------------------- *)


(** -------------------- Tactic in terms --------------------- *)


