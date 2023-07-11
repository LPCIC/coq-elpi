From elpi Require Import compiler.

Set partition_sub_goals.

Class InElpi (A : Set) (B : Set):= fElpi : A -> B.
Class InCoq (A B : Set) (P: InElpi A B):= fCoq : A -> B.

Global Instance e1 : InElpi bool bool := {fElpi a := a}.
Global Instance e2 : InElpi bool nat := {fElpi a := 0}.

(* Global Instance c1 : InCoq bool bool _ := {fCoq a := a}. *)
Global Instance c2 P : InCoq bool nat (P: InElpi bool nat) := {fCoq a := 0}.

Class Both  (A : Set) := fBoth : A -> A.
Global Instance both  (A B : Set) {eqa: InElpi A B} {eqb: InCoq A B _} : Both A := {fBoth a := a}.

Elpi AddAllClasses.
Elpi AddInstances both e2 e1 c2.
Elpi Override TC TC_solver All.

Elpi Accumulate TC_solver lp:{{
  :after "firstHook" 
  msolve L N :- coq.ltac.all (coq.ltac.open solve) L N.

  :after "firstHook"
  solve1 (goal Ctx _ Ty Sol _ as G) GL :-
  var Sol, not (prod _ _ _ = Ty), !, 
  build-context-clauses Ctx Clauses,
  @redflags! coq.redflags.beta => coq.reduction.lazy.norm Ty Ty1,
  Clauses => (tc-search-time Ty1 Proof),
    (
      coq.say "Solution " Proof,
      my-refine Proof G GL
    ).
}}.

Elpi Query TC_solver lp:{{
  sep.
}}.

Goal Both bool.
refine (both _ _).
Qed.