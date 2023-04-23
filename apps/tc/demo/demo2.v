Require Export Bool.
From elpi.apps Require Export tc.compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Elpi Override TC TC_check Only Eqb.
Elpi add_instances Eqb.

Elpi Print TC_check.

Check (eqb (tt, (tt, true)) (tt, (tt, true))).



