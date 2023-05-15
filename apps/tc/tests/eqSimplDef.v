Require Import Bool Arith List.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Global Instance eqU : Eqb unit := { eqb x y := true }.
Global Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Global Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.
(* Global Instance eqN : Eqb nat := { 
  eqb := fix add (a: nat) b := match a, b with 
  | 0, 0 => true 
  | S a, S b => add a b 
  | _, _ => false
  end }.

  
Check (forall n, n + n == 2 * n = true). *)