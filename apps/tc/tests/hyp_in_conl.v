From elpi.apps Require Import tc.

(* 
  Here we want to test that if the solution of a premise is rigid
  then the premise is not run
*)

Module M1.
  Structure ofe := Ofe { ofe_car : Type; }.

  Class D (I : ofe).

  Class C (X : ofe) (I : D X).

  Definition ofe_nat : ofe := Ofe nat.

  Instance c : forall (H : D (Ofe nat)), C ofe_nat H := {}.

  Goal forall (H : D (Ofe nat)), True -> exists H, C (ofe_nat) H.
    intros.
    notypeclasses refine (ex_intro _ _ _ ).
    apply _.
  Qed.
End M1.

Module M2.

  Class A.
  Class B (I : A).
  Class C (A : A) (I : B A).

  Instance c : forall (A : A) (B : B A), C A B := {}.

  Goal forall (A : A) (B : B A), exists A B, C A B.
    intros.
    do 2 notypeclasses refine (ex_intro _ _ _ ).
    apply _.
  Qed.

End M2.

Module M3.

  Class A.
  Class B (I : A).
  Class C (A : A) (I : B A).

  Instance c : forall (A : A) (B : B A), C A B := {}.

  Set Warnings "+elpi".

  Elpi Accumulate TC.Solver lp:{{
    :after "0"
    tc-elpi.apps.tc.tests.hyp_in_conl.M3.tc-A _ :- !, coq.error "Should not check for tc-A".
    tc-elpi.apps.tc.tests.hyp_in_conl.M3.tc-B _ _ :- !, coq.error "Should not check for tc-B".
  }}.
  Elpi Typecheck TC.Solver.

  Section s.
    Context (A : A) (B : B A).

    Definition d : C A B := _.
  End s.

End M3.