Require Export Bool Arith List.
From elpi.apps Require Export compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Elpi Override TC TC_check Only Eqb.
Elpi AddInstances Eqb.

Fail Check (fun n m : _ => eqb n m).

Goal (tt, (tt, true)) == (tt, (tt, true)) = true.
  easy.
Qed.

Fail Goal (1 == 2) = true.

Goal (@eqb _ eqU tt tt) = true. easy. Qed.

Goal (@eqb _ eqU tt tt) = true. easy. Qed.

(* Set Printing All.
Check (eqb (tt, (tt, true)) (tt, (tt, true))).

Check (@eqb _ _ (tt, 1) (tt, 2)). *)