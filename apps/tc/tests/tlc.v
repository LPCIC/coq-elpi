(* Test inspired from tlc library *)
From elpi Require Import tc.

Module extensionability.
  Notation binary A := (A -> A -> Prop).
  Class Extensionality (T : Type).
  Global Instance Extensionality_pred_2 
    (A1 : Type) (A2 : forall (x1 : A1), Type):
    Extensionality (forall (x1:A1) (x2:A2 x1), Prop). Qed.

  Goal forall A, Extensionality (binary A).
    intros.
    apply _.
  Qed.
End extensionability.