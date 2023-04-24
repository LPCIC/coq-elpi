Require Export Bool.
From elpi.apps Require Export tc.compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  tc _ _ A B :- std.spy-do![tc1 A B].

  pred tc1 o:term, o:term.
  tc1 {{Eqb unit}} {{eqU}}.
  tc1 {{Eqb bool}} {{eqB}}.
  tc1 {{Eqb (prod lp:A lp:B)}} {{@eqP _ _ lp:EqA lp:EqB}} :-

    std.spy-do![tc1 {{Eqb lp:A}} EqA], 
    std.spy-do![tc1 {{Eqb lp:B}} EqB]
    .
}}.
Elpi Typecheck TC_check.

(* Elpi Print TC_check. *)

Elpi Override TC TC_check Only Eqb.

Check (eqb (tt, (tt, true)) (tt, (tt, true))).



