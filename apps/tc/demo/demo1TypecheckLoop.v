Require Export Bool.
From elpi.apps Require Export compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.
(* Check (@eqP unit bool _ _ eqU eqB). *)
Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  tc _ _ A B :- tc1 0 A B.

  pred tc1 i:int, o:term, o:term.
  tc1 D {{Eqb unit}} {{eqU}} :- coq.say D "Found eqU".
  tc1 D {{Eqb bool}} {{eqB}} :- coq.say D "Found eqB".
  tc1 D {{Eqb (prod lp:A lp:B)}} {{@eqP _ _ _ _ lp:EqA lp:EqB}} :-
    coq.say D "Found eqP with two holes : ?EqA and ?EqB",
    D1 is D + 1,
    tc1 D1 {{Eqb lp:A}} EqA, 
    tc1 D1 {{Eqb lp:B}} EqB,
    coq.say D "Solved EqA:" EqA "and EqB:" EqB.
}}.
Elpi Typecheck TC_check.

(* Without the following line we run the coq solver *)
Elpi Override TC TC_check Only Eqb.
(* Check (@eqP unit bool _ _ eqU eqB). *)

Set Printing All.
Unset Typeclass Resolution For Conversion.
Check (@eqb _ _ (tt, (tt, true)) (tt, (tt, true))).



