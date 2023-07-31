Require Export Bool.
From elpi.apps Require Export compiler.
Elpi Debug "simple-compiler". 
Set AddModes.
Unset TC_NameFullPath.

(* Same example as before but with priority on instances *)

Class Eqb A : Type := eqb : A -> A -> bool.
Global Hint Mode Eqb + : typeclass_instances.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit | 10 := { eqb x y := true }.
Local Instance eqB : Eqb bool | 10 := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `(Eqb A, Eqb B) : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Elpi Override TC TC_solver Only Eqb.
Elpi AddClasses Eqb.
Elpi AddInstances Eqb.

(* Show how generated clauses are *)
(* Elpi Print TC_solver. *)

Check (eqb (tt, (tt, true)) (tt, (tt, true))).

(* This is an infinte loop without modes *)
Check (fun x y : _ => eqb x y).
