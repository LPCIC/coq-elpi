From elpi.apps Require Import tc.
Unset Typeclass Resolution For Conversion.
Unset TC_NameFullPath.
Elpi Override TC TC_solver All.


Class X (A: Type).
Class Y (A: Type).
Class Z (A: Type).

Local Instance Inst1@{i} {A: Type@{i}} : X A -> Y A. Qed. 
Local Instance Inst2@{i} (A : Type@{i}): (forall A : Type@{i}, X A -> Y A) -> Z A. Qed. 

(* TODO: here Elpi Trace Fails... *)

Goal forall A, Z A.
  intros.
  apply _.
Qed.