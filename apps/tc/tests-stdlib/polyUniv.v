From elpi.apps Require Import tc.
Elpi TC Solver Override TC.Solver All.

Polymorphic Definition pidentity {A : Type} (a : A) := a.
Polymorphic Definition selfpid := pidentity (@pidentity).

Class C A (H : A -> A) (Z : forall A, A -> A)  := {}.

Set Printing Universes.
About C.

Elpi Accumulate TC.Solver lp:{{
  tc.print-goal.
  tc.print-compiled-goal.
  tc.print-post-process-goal.
}}.

Instance I A : C A pidentity selfpid. Qed.

Goal forall A, C A pidentity selfpid.
  intro H.
  apply _.
Qed.

