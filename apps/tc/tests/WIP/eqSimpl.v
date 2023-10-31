(* 
  TODO: modes don't work, since, when compiled, instance does 
  not already know them 
*)
Require Import Bool.
From elpi.apps Require Import tc.

Elpi Debug "simple-compiler".
Set TC AddModes.

Class MyEqb A : Type := eqb : A -> A -> bool.
Global Hint Mode MyEqb + : typeclass_instances.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Global Instance eqU : MyEqb unit := { eqb x y := true }.
Global Instance eqB : MyEqb bool := { eqb x y := if x then y else negb y }.
Global Instance eqP {A B} `{MyEqb A} `{MyEqb B} : MyEqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Fail Check (fun n m : _ => eqb n m).

Goal (tt, (tt, true)) == (tt, (tt, true)) = true.
  easy.
Qed.

