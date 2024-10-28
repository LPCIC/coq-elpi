From elpi Require Import tc.
Require Import Bool.

Module m1.
  #[mode(g)] Elpi TC.Pending_attributes.
  Class C (i : nat).
  Instance C0 : C 0. Qed.
  Goal exists x, C x. eexists. Fail apply _. Abort.
  Class C' (i : nat).
  Instance C0' : C' 0. Qed.
  Goal exists x, C' x. eexists. apply _. Abort.

  #[mode(g)] TC.Pending_attributes.
  Fail #[mode(g)] TC.Pending_attributes.

  Class C'' (i : nat).
  Instance C0'' : C'' 0. Qed.
  Goal exists x, C'' x. eexists. Fail apply _. Abort.
End m1.

Module ground.
  #[mode(g)] TC.Pending_attributes.
  Class C (i : Type).
  Instance i : C (list nat). Qed.

  Goal exists (x : Type), C (list x). 
    eexists. 
    Fail apply _.
  Abort.
End ground.

Module ground1.
  #[mode(g)] TC.Pending_attributes.
  Class C (i : Type).
  Instance i x: C x. Qed.

  Goal exists (x : Type), C (list x). 
    eexists.
    apply _.
  Abort.
End ground1.

Module ground2.
  #[mode(g)] TC.Pending_attributes.
  Class C (i : Type).
  Instance i (x: Type): C (list x). Qed.

  Goal exists (x : Type), C (list x). 
    eexists. 
    apply _.
  Abort.
End ground2.

Module ground3.
  #[mode(g,g)] TC.Pending_attributes.
  Class C {i : Type} (f : i -> i -> Prop).
  Instance i {X : Type}: C (@eq X). Qed.
  Hint Mode C ! ! : typeclass_instances.

  Goal exists (X : Type), C (@eq X). 
    eexists.
    Fail apply _.
  Abort.
End ground3.

Module ground4.
  #[mode(o,g)] TC.Pending_attributes.
  Class C {i : Type} (f : i -> i -> Prop).
  Instance i {X : Type}: C (@eq X). Qed.

  Goal exists (X : Type), @C (list X) eq. 
    eexists.
     apply _.
  Abort.
End ground4.

Module rigid_head1.
  #[mode(i)] TC.Pending_attributes.
  Class C (i : Type).
  Instance i: C (list nat). Qed.

  Goal exists (x : Type), C (list x). 
    eexists.
    apply _.
  Qed.

  Goal exists (x : Type), C x. 
    eexists.
    (* This fails since x is flex and mode i accepts only terms with rigid head *)
    Fail apply _.
  Abort.
End rigid_head1.

Module rigid_head2.
  #[mode(i,i)] TC.Pending_attributes.
  Class C {i : Type} (f : i -> i -> Prop).
  Instance i {X : Type}: C (@eq X). Qed.

  Goal exists (X : Type), C (@eq X). 
    eexists.
    Fail apply _.
  Abort.
End rigid_head2.

Module simplEq.

  #[mode(i)] TC.Pending_attributes.
  Class MyEqb A : Type := eqb : A -> A -> bool.
  (* Global Hint Mode MyEqb ! : typeclass_instances. *)

  Notation " x == y " := (eqb x y) (no associativity, at level 70).

  Global Instance eqU : MyEqb unit := { eqb x y := true }.
  Global Instance eqB : MyEqb bool := { eqb x y := if x then y else negb y }.
  Global Instance eqP {A B} `{MyEqb A} `{MyEqb B} : MyEqb (A * B) := { 
    eqb x y := (fst x == fst y) && (snd x == snd y) }.

  Fail Goal exists T: Type, forall n m : T, eqb n m = false.
  Goal forall n m : bool, eqb n m = false. Abort.
End simplEq.

Module force_input_link.
  #[mode(g)] TC.Pending_attributes.
  Class A (i: nat -> nat -> nat).

  Global Hint Mode A + : typeclass_instances.

  Axiom (f : nat -> nat -> nat).
  Instance instA: A f := {}.

  Class B (i: nat).
  Instance instB : forall R, A R -> forall x y, B (R x y) := {}.
  
  Goal B (f 0 0).
    apply _.
  Qed.
End force_input_link.

Module force_input_link_HO_var1.

  #[mode(i)] TC.Pending_attributes.
  Class A (i: Type).
  Global Hint Mode A ! : typeclass_instances. (*Mode also added in elpi*)

  Axiom f : Type -> Type.
  Axiom g : Type -> Type.

  Class B (i :Type).

  (* Elpi Trace Browser. *)
  Instance i: forall X (Y: Type), (forall Y, A (X Y)) -> B (X Y) := {}.
  Instance a : forall x, A (g x) := {}.
  Instance b x : A (f x) -> A (f x) := {}.

  
  Goal B (g nat).
    apply _.
  Qed.

End force_input_link_HO_var1.

Module force_input_link_HO_var2.

  #[mode(i)] TC.Pending_attributes.
  Class A (i: Type).
  Global Hint Mode A ! : typeclass_instances. (*Mode also added in elpi*)

  Axiom f : Type -> Type.
  Axiom g : Type -> Type.

  Class B (i :Type).

  Instance i: forall X (Y: Type), A (X Y) -> B (X Y) := {}.
  Instance a : A (g nat) := {}.
  Instance b x : A (f x) -> A (f x) | 0 := {}.

  Goal B (g nat).
    apply _.
  Abort.

End force_input_link_HO_var2.

Module force_input_link_HO_var3.

  #[mode(i)] TC.Pending_attributes.
  Class A (i: Type).
  Global Hint Mode A ! : typeclass_instances. (*Mode also added in elpi*)

  Axiom g : Type -> Type.

  Class B (i :Type).

  (* TODO: This instance should not be compilable ? 
           The premise has always a flex term while its mode is rigid head *)
  Instance i: forall X (Y: Type), (A X) -> B nat := {}.
  Instance b x : A x -> A x := {}.

  Goal B nat.
    (* TODO: this should not loop, note that we have no way to stop it in elpi
             since the current modes on arguments do not filter out instance b 
    *)
    Fail Timeout 1 apply _.
  Abort.

End force_input_link_HO_var3.
