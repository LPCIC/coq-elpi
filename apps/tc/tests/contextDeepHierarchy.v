From elpi.apps Require Import compiler.

Class X (A: Type).
Class Y (A: Type).
Class Z (A: Type).

Local Instance Inst1 {A: Type} : X A -> Y A. Qed. 
Local Instance Inst2 A: (forall A, X A -> Y A) -> Z A. Qed. 

Elpi Override TC TC_check All.
Elpi AddAllInstances.
Unset Typeclass Resolution For Conversion.

Goal forall A, Z A.
(* TODO: here Elpi Trace Fails... *)
(* Elpi Trace Browser. *)
  apply _.
Qed.