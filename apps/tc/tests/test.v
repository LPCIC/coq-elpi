From elpi Require Import tc.

Module simpleHO.
  Class A (t : nat -> nat) (t' : Type).
  Class B (t : nat) (t' : Type).

  Instance I1: forall b (c : nat -> nat),
    (forall a, B (c a) b) -> A c b.
  Qed.

  Instance I2 : B 3 bool. Qed.

  Goal exists x, A x bool.
  Proof. 
    eexists.
    apply _.
  Qed.
End simpleHO.

Module HO_1.
  Class A (t : nat -> nat -> nat -> nat).
  Class B (t : nat -> nat -> nat).
  Class C (t : nat).

  Axiom (f : nat -> nat -> nat -> nat).

  Instance I1: forall a b, (C (f a b 3)). Qed.
  Instance I2: forall F, (forall x y, C (F x y)) -> B (fun a b => F a b). Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A (fun x y z => F x y z). Qed.

  Goal exists x, A x.
    eexists.
    apply _.
    Unshelve. 
    (* Note: here we find a most general solution then Coq's one *)
    all: apply 3.
  Qed.

End HO_1.

Module HO_2.
  Class A (t : nat -> nat -> nat -> nat -> nat -> nat).
  Class B (t : nat -> nat -> nat -> nat -> nat).
  Class C (t : nat -> nat -> nat).

  Axiom (f : nat -> nat -> nat -> nat).

  Instance I1: C (fun x => f x 3). Qed.
  Instance I2: forall F, (forall x y, C (F x y)) -> B (fun a b => F b a). Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal exists x, A x.
    eexists.
    apply _.
  Qed.
End HO_2.


(* Module HO_swap.
  Axiom (f : Type -> Type -> Type).

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).

  Instance a1 : forall (F : Type -> Type -> Type), 
    c2 (fun x y => F y x) -> c1 F. Qed.

  Instance b1 : c2 f. Qed.

  (* Here use of maybe-eta *)
  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_swap. *)
