From elpi Require Import tc.

Module simpleHO.
  Class A (t : nat -> nat) (t' : Type).
  Class B (t : nat) (t' : Type).

  Instance I1: forall F c, (forall a, B (F a) c) -> A F c. Qed.
  Instance I2 : B 3 bool. Qed.
  Goal exists x, A x bool.
  Proof. 
    eexists.
    apply _.
  Qed.
End simpleHO.

Module HO_1.
  Axiom (f : bool -> unit -> nat -> nat).
  
  Class A (t : bool -> unit -> nat -> nat).
  Class B (t : unit -> nat -> nat).
  Class C (t : nat).

  Instance I1: forall a b, (C (f true a b)). Qed.
  Instance I2: forall F, (forall x y, C (F x y)) -> B F. Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal B (fun x y => f true x y).
    apply _.
  Abort.

  Goal exists x, A x.
    eexists.
    apply _.
    Unshelve. 
    (* Note: here we find a most general solution than Coq's one *)
    apply tt.
    apply 3.
  Qed.
End HO_1.

Module HO_2.
  Axiom f : Type -> Type -> Type.

  Class A (t : Type -> Type -> Type) (t : Type -> Type -> Type).

  Instance I: forall f, A f (fun x y => f y x). Qed.
  
  Goal A f (fun x y => f y x).
    apply _.
  Qed.
End HO_2.

Module HO_3.
  Axiom (f : nat -> nat -> nat).

  Class A (t : nat -> nat -> nat -> nat).
  Class B (t : nat -> nat -> nat).
  Class C (t : nat -> nat).

  Instance I1: (C (f 3)). Qed.
  (* Instance I2: forall F, (forall x, C (F x)) -> B (fun a => F a). Qed. *)
  (* Instance I3: forall F, (forall x, B (F x)) -> A (fun x => F x). Qed. *)
  Instance I2: forall F, (forall x, C (F x)) -> B F. Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal exists x,B x.
    eexists.
    apply _.
  Qed.
End HO_3.


Module HO_4.
  Axiom (f : nat -> nat -> nat -> nat).

  Class A (t : nat -> nat -> nat -> nat -> nat -> nat).
  Class B (t : nat -> nat -> nat -> nat -> nat).
  Class C (t : nat -> nat -> nat).

  Instance I1: C (fun x => f x 3). Qed.
  Instance I2: forall F, (forall x y, C (F x y)) -> B (fun a b => F b a). Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal exists x, A x.
    eexists.
    apply _.
  Qed.
End HO_4.


Module HO_swap.
  Axiom (f : Type -> Type -> Type).
  Elpi Query TC.Solver lp:{{
    link.maybe-eta (fun `x` _ c0 \ fun `y` _ c1 \ A2 c1 c0),
    link.maybe-eta (fun `x` _ c0 \ fun `y` _ c1 \ A2 (A c1) c0),
    link.maybe-eta {{fun x y => f x y}}.
  }}.

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).

  Instance a1 : forall (F : Type -> Type -> Type), 
    c2 (fun x y => F y x) -> c1 F. Qed.

  Instance b1 : c2 f. Qed.

  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_swap.

Module HO_hard.

  Class A (i: nat -> nat).
  Class B (i: nat -> nat).

  Instance I1: forall f g, B g -> A (fun x => f (g x)). Qed.
  Instance I2: B (fun x => x). Qed.

  Goal A S.
    apply _.
  Qed.

End HO_hard.

Module HO_5.
  Axiom (f : Type -> Type -> Type).

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).
  Class c3 (T : (Type -> Type -> Type)).

  Instance a1 : forall (F : Type -> Type -> Type), 
    (c2 (fun x y => F y x) -> c3 (fun x y => F y x)) -> c1 F. Qed.

  Instance a2 : c2 f -> c3 f. Qed.

  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_5.


Module HO_6.
  Axiom (f : Type -> Type -> Type).

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).
  Class c3 (G : nat -> nat) (T : (Type -> Type -> Type)).

  Instance a1 : forall (F : Type -> Type -> Type), 
    (c2 (fun x y => F y x) -> 
      forall G, c3 G (fun x y => F y x)) -> 
    c1 F. 
  Qed.
  Elpi Print TC.Solver.
  Elpi Trace Browser.

  Instance a2 : forall F, c2 f -> c3 F f. Qed.

  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_6.
