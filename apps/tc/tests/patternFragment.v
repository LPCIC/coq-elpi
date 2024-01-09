From elpi.apps Require Import tc.
Elpi Override TC TC.Solver All.
Set TC NameShortPath.
Set TC CompilerWithPatternFragment.

Class Y (A: Type).
Class Z (A: Type).
Class Ex (P : Type -> Type) (A: Type).

Module M4.
Local Instance Inst2 A F: (forall (a : Type) (b c : nat), Y (F a b) -> Y (F a c)) -> Z A. Qed.
Elpi Print TC.Solver.
Goal Z bool.
(*
tc-Z A3 (app [global (const «Inst2»), A3, A2, A0]) :-
 pi c0 \
  decl c0 `a` (sort (typ A6)) =>
   pi c1 \
    decl c1 `b` (global (indt «nat»)) =>
     pi c2 \
      decl c2 `c` (global (indt «nat»)) =>
       pi c3 \
        decl c3 `_` (app [global (indt «Y»), app [A2, c0, c1]]) =>
         do
          [(tc-Y (A1 c0 c1) c3 :-
             coq.reduction.eta-contract (fun `a` (sort (typ A6)) c4 \ A1 c4) A2) =>
             
             tc-Y (A1 c0 c2) (A0 c0 c1 c2 c3), 

           coq.reduction.eta-contract (fun `a` (sort (typ A6)) c4 \ A1 c4) A2].

*)
Elpi Override TC TC.Solver None.
  Fail apply _.
Elpi Override TC TC.Solver All.
Elpi Trace Browser.
  apply _.
  Show Proof.
  Unshelve. assumption. (* we keep a, the first arg of F *)
  Show Proof. Qed.

Local Instance Inst1: Y (bool * bool). Qed.

Goal Z bool.

Elpi Override TC TC.Solver None.
  Succeed apply _. 
Elpi Override TC TC.Solver All.
  apply _.

  Show Proof.
  Unshelve. apply bool.
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

