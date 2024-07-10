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

  Section s.
    Elpi Accumulate TC.Solver lp:{{
      :before "0" tc-elpi.apps.tc.tests.hyp_in_conl.M3.tc-A _   :- coq.say "In tc-A", fail.
      :before "0" tc-elpi.apps.tc.tests.hyp_in_conl.M3.tc-B _ _ :- coq.say "In tc-B", fail.
    }}.
    Elpi Typecheck TC.Solver.
    Local Instance AX : A := {}.
    Local Instance BX : A -> (B AX) := {}.

    Elpi Accumulate TC.Solver lp:{{ print-goal. print-solution. }}.
    Definition d : C AX (BX _) := _.
    Definition d' : C _ (BX _) := _.
    Definition d'' : C AX _ := _.

    Check (c _ _) : C AX _.

    (* 
      Here we give the solver a partial solution with a hole in it. This hole
      correspond to the premise of the typeclass B (an instance of A). Due to
      the var condition on the resolution of rule's premises, the premise of
      `C`, that is, `B X` is not solved since we have the partial solution `BX
      _`. (see: [here](https://github.com/LPCIC/coq-elpi/blob/889bd3fc16c31f35c850edf5a0df2f70ea9c655a/apps/tc/elpi/tc_aux.elpi#L124))
    *)
    Elpi Query TC.Solver lp:{{
      S = {{c AX (BX _)}},
      solve-aux1 [] {{C _ _}} S.
    }}.

  End s.

End M3.