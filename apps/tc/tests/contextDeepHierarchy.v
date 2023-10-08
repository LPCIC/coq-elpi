From elpi.apps Require Import tc.
Unset Typeclass Resolution For Conversion.
Unset TC_NameFullPath.
(* Elpi Debug "simple-compiler". *)
Elpi Override TC TC_solver All.


Class X (A: Type).
Class Y (A: Type).
Class Z (A: Type).
Elpi AddClasses X Y Z.

Local Instance Inst1@{i} {A: Type@{i}} : X A -> Y A. Qed. 
Local Instance Inst2@{i} (A : Type@{i}): (forall A : Type@{i}, X A -> Y A) -> Z A. Qed. 

Elpi AddAllInstances.

(* Elpi Print TC_solver "TC_solver.html" ".*: [0-9]+.*". *)

(*Print Universes.*)

Set Printing Universes. Set Printing All.

(* TODO: here Elpi Trace Fails... *)
(* Elpi Trace Browser. *)

Goal forall A, Z A.
  intros.
  apply _.

  (* Elpi Override TC TC_solver None. *)
  (*refine (fun (A : Type) => Inst2 A (@Inst1)).*)
  (* apply _. *)
   Show Proof.
Qed.

(* Good : (fun A : Type => Inst2 A (@Inst1)) *)
(* Not Good : (fun A : Type => Inst2 A (fun (H : ?elpi_evar) (H0 : ?elpi_evar0@{y:=H}) => Inst1 H0)) *)