From Coq Require Import Setoid.

Module B.
  Class Persistent (A: Prop).
  Class Separable (A: Prop).
  Local Instance persistent_separable P:
    Persistent P -> Separable P | 10.
  Admitted.
  Local Instance and_persistent P Q : 
    Persistent P -> Persistent Q -> Persistent (P /\ Q) | 0.
  Admitted.
  Local Instance and_separable P1 P2 : 
    Separable P1 -> Separable P2 -> Separable (P1 /\ P2) | 0.
  Admitted.

  Goal forall (P Q : Prop), Persistent (P /\ Q) <-> Persistent (Q /\ P).
  intros.
  split.
  intros.
  apply and_persistent.
  .
  rewrite and_comm.
  destruct Persistent.

  Goal forall (P Q: Prop), Persistent P -> Persistent Q -> Separable (P /\ Q).
    apply _.
  Qed.
  Goal forall (P Q R: Prop), Persistent (P) -> Persistent (R /\ Q) -> Separable (P /\ Q /\ R).
    intros.
    apply _.
  Qed.

  From elpi Require Import compiler.
  Elpi AddAllInstances.
  Elpi Override TC TC_solver All.
  Goal forall (P Q R: Prop), Persistent P -> Persistent (Q /\ R) -> Separable (P /\ Q /\ R).
    apply _.
  Qed.
End B.