Require Export Bool.
From elpi.apps Require Export compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `(Eqb A, Eqb B) : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.
Check (eqP eqU eqB).
Elpi Accumulate TC_solver lp:{{
  tc _ {{Eqb unit}} {{eqU}}.
  tc _ {{Eqb bool}} {{eqB}}.
  tc _ {{Eqb (prod lp:A lp:B)}} {{eqP lp:EqA lp:EqB}} :-
    tc _ {{Eqb lp:A}} EqA, 
    tc _ {{Eqb lp:B}} EqB.

  % Comment the before lines in order to launch tc2
  tc _ A B :- tc2 0 A B.
  pred tc2 i:int, o:term, o:term.
  tc2 D {{Eqb unit}} {{eqU}} :- coq.say D "Found eqU".
  tc2 D {{Eqb bool}} {{eqB}} :- coq.say D "Found eqB".
  tc2 D {{Eqb (prod lp:A lp:B)}} {{eqP lp:EqA lp:EqB}} :-
    coq.say D "Found eqP with two holes : ?EqA and ?EqB",
    D1 is D + 1,
    tc2 D1 {{Eqb lp:A}} EqA, 
    tc2 D1 {{Eqb lp:B}} EqB,
    coq.say D "Solved EqA:" EqA "and EqB:" EqB.
}}.
Elpi Typecheck TC_solver.

(* Without the following line we run the coq solver *)
Elpi Override TC TC_solver Only Eqb.
(* Check (@eqP unit bool _ _ eqU eqB). *)

Set Printing All.
Check (eqb (tt, (tt, true)) (tt, (tt, true))).