From elpi Require Import tc.

Module simpleHO.
  Class A (t : nat -> nat) (t' : Type).
  Class B (t : nat) (t' : Type).

  Instance Innnn: forall b (c : nat -> nat),
    (forall a, B (c a) b) -> A c b.
  Qed.

  Instance Immmm : B 3 bool. Qed.

  Goal exists x, A x bool.
  Proof. 
    eexists.
    apply _.
  Qed.
End simpleHO.

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
