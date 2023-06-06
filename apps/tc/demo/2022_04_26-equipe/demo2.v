Require Export Bool.
From elpi.apps Require Export compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqP {A B} `(Eqb A, Eqb B) : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

(* Here we override all the TC *)
Elpi Override TC TC_solver All.
Elpi AddInstances Eqb.

(* Show how generated clauses are with the HTML file *)
(* Elpi Print TC_solver. *)

Check (eqb (tt, (tt, true)) (tt, (tt, true))).

(* Invalid mode here... *)
Elpi Query TC_solver lp:{{
  coq.warning "" "" "following should fail".
}}.
(* Fail Check (fun x y : _ => eqb x y). *)

(* We are able to come back to Coq by removing the Eqb override *)
Elpi Override TC - Eqb.

Check (fun x y : _ => eqb x y).
