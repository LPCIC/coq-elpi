From elpi Require Import compiler.
Elpi Debug "simple-compiler".
Unset TC_NameFullPath.


Class C (n : nat).
Local Instance c_1 : C 1 | 10. Qed.
Local Instance c_2 : C 2 | 1. Qed.

Class D (n : nat).
Local Instance d_1 : D 1. Qed.

Class E (n : nat).
Local Instance foo {n} : 
  C n -> D n -> E n. Qed.

#[deterministic] Elpi AddClasses C.
Elpi AddClasses D E.
Elpi AddAllInstances.

Elpi Override TC TC_solver All.
(* Elpi Trace Browser. *)
Check (_ : E _).