Require Export Bool.
From elpi.apps Require Export tc.compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Elpi Accumulate TC_check lp:{{
  tc _ _ {{Eqb unit}} {{eqU}} :- coq.say "Found Eq for Unit".
  tc _ _ {{Eqb bool}} {{eqB}} :- coq.say "Found Eq for bool".
  tc _ _ {{Eqb (prod lp:A lp:B)}} {{@eqP _ _ lp:EqA lp:EqB}} :-
    coq.say "Found Eq for Prod ?EqA ?EqB",
    tc TC_ In_ {{Eqb lp:A}} EqA, 
    tc TC_ A_ {{Eqb lp:B}} EqB,
    coq.say "?EqA is" EqA ", EqB is" EqB.
}}.
Elpi Typecheck TC_check.

Elpi Override TC TC_check All.
Elpi Print TC_check.

(* Elpi Trace Browser. *)

Check (eqb (tt, (tt, true)) (tt, (tt, true))).



