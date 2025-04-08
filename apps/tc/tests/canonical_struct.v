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
  Structure ofe := Ofe { ofe_car :> Type; }.
  Structure cmra := Cmra { cmra_car :> Type; }.

  Coercion cmra_ofeO (A : cmra) := Ofe A.

  Elpi Accumulate tc.db lp:{{
    tc.coercion-unify {{cmra_ofeO}}.
  }}.

  Canonical Structure ofe_nat := Ofe nat.
  Canonical Structure cmra_nat := Cmra nat.

  Class C (i: ofe).

  Instance i: forall (c : cmra), C (cmra_ofeO c) := {}.

  Goal C ofe_nat.
    apply _.
  Qed.
End CS6.

Module CS7.
  Structure ofe := Ofe { ofe_car :> Type; }.
  Structure cmra := Cmra { cmra_car :> Type; }.

  Coercion cmra_ofeO (A : cmra) := Ofe A.

  Elpi Accumulate tc.db lp:{{
    tc.coercion-unify {{cmra_ofeO}}.
  }}.

  Canonical Structure ofe_bool := Ofe bool.
  Canonical Structure cmra_bool := Cmra bool.

  Class C (i: ofe).

  Class D (i: Type).
  Instance d : D bool := {}.

  Instance i: forall (c : cmra), D (cmra_car c) -> C (cmra_ofeO c) := {}.
  Elpi Print TC.Solver.

  Goal C ofe_bool.
    apply _.
  Qed.

  Canonical Structure ofe_nat := Ofe nat.
  Canonical Structure cmra_nat := Cmra nat.

  Goal exists a, C a.
    eexists.
    apply _.
  Qed.
End CS7.

Module CS8.
  Structure ofe := Ofe { ofe_car :> Type; }.
  Canonical Structure ofe_bool := Ofe bool.
  Class C (i : Type).
  Instance i : C ofe_bool := {}.

  (* 
    Test for constraint activation using tc.link.solve-cs: After
    tc-instance-search, we have the suspended goal `tc.link.cs X ofe_bool` that
    must be activated. This activation need to load the context before the 
    call to unify-eq since we need to load the type of `x`
  *)
  Goal forall (x: nat), exists X, C X.
    eexists. apply _.
  Qed.

  (* TODO: error in llam link *)
  (* Goal forall (x: nat), exists X, C (X x).
    eexists.
    Elpi Trace Browser.
    (* Elpi TC Solver Deactivate TC.Solver. *)
    apply _.
  Qed *)
End CS8.

Module CS9.
  Structure ofe := Ofe { ofe_car :> Type; }.
  Canonical Structure ofe_bool := Ofe bool.
  Canonical Structure ofe_nat := Ofe nat.

  Class loop.
  Instance l : loop -> loop := {}.
  Class C (i : Type) (i : Type).
  Instance i : loop -> C ofe_bool ofe_nat := {}.

  (* 
    Here we have two suspended goal on X with cs links. The same variable
    is linked with ofe_bool and ofe_nat. Since they don't unfy, the instance
    `i` cannot be used.
  *)
  Goal exists X, C X X.
    eexists.
    Fail apply _.
  Abort.
End CS9.

Module CS10.
  Structure ofe := Ofe { ofe_car :> Type; }.
  Canonical Structure ofe_bool := Ofe bool.

  Class C (i : Type).
  Instance i : C bool := {}.

  (* Here the projection is in the goal *)
  Goal C (ofe_car ofe_bool). apply _. Qed.
End CS10.

Module CS11.
  Structure ofe := Ofe { ofe_car :> Type; }.
  Canonical Structure ofe_bool := Ofe bool.

  Class D (i : ofe).
  Instance d : D (ofe_bool) := {}.

  Class C (i : Type).
  Instance i X:  D X -> C (ofe_car X) := {}.

  (* Here the projection is in the goal *)
  Goal exists X, C (ofe_car X). eexists.
    apply _.
    Show Proof.
  Qed.
