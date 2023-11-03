From elpi.apps Require Import tc.
Elpi Override TC TC_solver All.
Set TC NameShortPath.
Set TC CompilerWithPatternFragment.

Class Y (A: Type).
Class Z (A: Type).
Class Ex (P : Type -> Type) (A: Type).

Module M4.
Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a b c : Type), Y (F a b) -> Y (F b c)) -> Z A. Qed.
Goal Z bool.
  apply _.
  Show Proof.
  Unshelve. apply nat.
  Show Proof. Qed.
End M4.

Module M5.
Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F (R: Type -> Type -> Type):  forall x,
  (forall (a : Type), Y (F a)) -> Ex (R x) A. Qed.
Goal forall (A:Type) x (R: Type -> Type -> Type ->Type), Ex (R x x) A. apply _. Qed.
End M5.

Module M1.
Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a : Type), Y (F a)) -> Z A. Qed.

Goal forall (A:Type), Z A. apply _. Qed.
End M1.

Module M2.
Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a: Type), Y (F a)) -> Z A. Qed.
Goal Z bool. apply _. Qed.
End M2.

Module M3.
Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a b c d: Type), Y (F b c d)) -> Z A. Qed.
Goal Z bool. apply _. Qed.
End M3.

Module M6.
Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a b c d e f g: Type), Y (F a b c d) -> Y (F e f g a)) -> Z A. Qed.
Goal Z bool. apply _. Unshelve. apply nat. Qed.
End M6.

Module M1b.
Local Instance Inst2 A F: (forall (a : Type), Y (F a)) -> Ex F A. Qed.
Goal forall (A:Type) (f : Type -> Type), (forall x, Y (f x)) -> exists f, Ex f A. intros. eexists. apply _. 
  Unshelve. 
  apply A. 
Qed.
End M1b. 

