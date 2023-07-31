From elpi Require Import compiler.
Elpi Debug "simple-compiler".
Unset TC_NameFullPath.

Elpi Override TC TC_solver All.

Module M1.
  Class C1 (A : Type).
  Elpi AddAllClasses.

  Local Instance I1 : C1 nat. Admitted.
  #[local] Elpi AddAllInstances.

  Goal C1 nat. apply _. Qed.

  Definition nat' := nat.


  Elpi Print TC_solver.
  Elpi Trace Browser.
  Goal C1 nat'. Fail apply _. Abort.

  Elpi Accumulate TC_solver lp:{{
    tc-C1 {{nat'}} Sol :- 
      tc-C1 {{nat}} Sol.
  }}.

  Goal C1 nat'. apply _. Qed.
End M1.

(*----------------------------------------------------*)

Require Import Program.Basics.

Class C2 {A B} (f : A -> B).
Elpi AddClasses C2.

Local Instance I2 {A B C} (f : A -> B) (g : B -> C) : C2 (compose g f). Admitted.
Elpi AddInstances I2.

Goal C2 (compose S S). apply _. Qed.

Elpi Accumulate TC_solver lp:{{
  tc-C2 A B D Sol :- 
    coq.unify-eq D {{fun x => lp:F (lp:G x)}} ok,
    tc-C2 A B {{compose lp:F lp:G}} Sol.
}}.
Elpi Typecheck TC_solver.

Goal C2 (fun x => S (id x)). apply _. Qed.

(*----------------------------------------------------*)

Class Y (A: Type).
Class Z (A: Type).

Elpi AddAllClasses.

Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a: Type), Y (F a)) -> Z A. Qed.
Elpi AddAllInstances.
Elpi Print TC_solver.
Goal Z bool. Fail apply _. Abort.

Elpi Accumulate TC_solver lp:{{
  tc-Z A S :- 
    pi x\ tc-Y (F x) S1, 
    S = {{ Inst2 lp:A (fun _ => lp:{{F x}}) (fun _ => lp:S1) }}.
}}.
Elpi Typecheck TC_solver.

(* Elpi Trace Browser. *)

Goal Z bool. apply _. Qed.
