From elpi.apps Require Import compiler.

Class X (A: Type).
Class Z (A: Type).

Local Instance X1 {A: Type} : X A. Qed. 

Elpi Override TC TC_check All.
Elpi AddAllInstances.

Goal forall A, (forall A, X A -> Z A) -> Z A.
  apply _.
Qed.

Fail.