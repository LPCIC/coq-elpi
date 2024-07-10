From elpi.apps Require Import tc.

Module CS1.

  Structure ofe := Ofe {
    ofe_car :> Type;
  }.
  Canonical ofe_nat : ofe := Ofe nat.

  Class C (I : Type).

  Instance c : C (ofe_car ofe_nat). Qed.
  Goal C (Ofe nat). apply _. Qed. (* No CS search *)
  Goal exists x, C (Ofe x). eexists. apply _. Qed. (* CS Search to assign x *)
  Goal C (ofe_car ofe_nat). apply _. Qed.

End CS1.

Module CS2.
  Structure ofe := Ofe {
    ofe_car :> Type;
  }.
  Canonical ofe_nat : ofe := Ofe nat.

  Class C (I : Type).

  Instance c : C (Ofe nat). Qed.
  Goal C (Ofe nat). apply _. Qed. (* No CS search *)
  Goal exists x, C (Ofe x). eexists. apply _. Qed. (* CS Search to assign x *)
  Goal C (ofe_car ofe_nat). apply _. Qed.

End CS2.

(* With primitive projection *)
Module CS3.
  Class C (I : Type).

  #[local] Set Primitive Projections.
  Structure ofe := Ofe {
    ofe_car :> Type;
  }.
  Canonical ofe_nat : ofe := Ofe nat.

  Instance c : C ofe_nat.(ofe_car). Qed.
  Goal C (Ofe nat). apply _. Qed. (* No CS search *)
  Goal exists x, C (Ofe x). eexists. apply _. Qed. (* CS Search to assign x *)
  Goal C (ofe_car ofe_nat). apply _. Qed.

End CS3.

Module CS4.
  Class C (I : Type).

  #[local] Set Primitive Projections.
  Structure ofe := Ofe {
    ofe_car :> Type;
  }.
  Canonical ofe_nat : ofe := Ofe nat.

  Instance c : C (Ofe nat).(ofe_car). Qed.
  Goal C (Ofe nat). apply _. Qed. (* No CS search *)
  Goal exists x, C (Ofe x). eexists. apply _. Qed. (* CS Search to assign x *)
  Goal C (ofe_car ofe_nat). apply _. Qed.

End CS4.

(* With bound variables *)
Module CS5.
  Structure ofe := Ofe {
    ofe_car :> Type;
  }.
  Canonical ofe_any x : ofe := Ofe x.

  Class C (I : Type -> Type).
  Axiom f : ofe -> Type.

  Instance c X : C (fun x => (Ofe (f (X x)))). Qed.
  Goal C (fun x => (Ofe (f x))). apply _. Qed. (* No CS search *)
  Goal C (fun (_: Type) => Ofe (f nat)). apply _. Qed. (* CS Search to assign x *)
  Goal exists X, C (fun y => ofe_car (X y)). eexists.
    apply _.
    Unshelve.
    apply (ofe_any nat).
  Qed.

  Lemma coq_unif_fail: exists X Y, (fun (y: Type) => ofe_car (X y)) = (fun _ => Y).
    do 2 eexists.
    Fail reflexivity.
  Abort.
    
  Goal exists Z, C (fun _ => Z). eexists.
    (* 
      Note that here, coq8.20 unification algorithm would fail to unify
      with error 
        Unable to unify "?Y" with "ofe_car (?X x)" as "ofe_car (?X x)" 
        contains local variables.
    *)
    apply _.
    Unshelve.
    apply (ofe_any nat).
  Qed.
End CS5.

Module CS6.
  #[projections(primitive=yes)]
  Structure ofe := Ofe { ofe_car : Type; }.

  #[projections(primitive=no)] (* TODO: Putting primitive to yes leads to a unification error. Why? *)
  Structure cmra := { cmra_car :> Type; }.
  Canonical Structure cmra_ofeO (A : cmra) : ofe := Ofe A.

  Class C (I : Type).
  Instance c : forall (A : ofe), C ((A).(ofe_car)) := {}.

  Section s.
    Context {cmra : cmra}.
    Goal C (cmra_car cmra).
      apply _.
    Qed.
  End s.
End CS6.
