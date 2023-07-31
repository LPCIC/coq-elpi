Require Export Bool.
From elpi.apps Require Export compiler.

Unset TC_NameFullPath.

Class Eqb A : Type := eqb : A -> A -> bool.
Elpi AddClasses Eqb.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `(Eqb A, Eqb B) : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.
Check (eqP eqU eqB).
Elpi Accumulate TC_solver lp:{{
  tc-Eqb {{unit}} {{eqU}}.
  tc-Eqb {{bool}} {{eqB}}.
  tc-Eqb {{prod lp:A lp:B}} {{@eqP lp:A lp:B lp:EqA lp:EqB}} :-
    tc-Eqb A EqA,
    tc-Eqb B EqB.

  % Comment the before lines in order to launch tc2
  :after "firstHook"
  tc A B :- !, tc2 0 A B, coq.say "The final solution is" {coq.term->string B}.
  pred tc2 i:int, o:term, o:term.
  tc2 D {{Eqb unit}} {{eqU}} :- coq.say D "Found eqU".
  tc2 D {{Eqb bool}} {{eqB}} :- coq.say D "Found eqB".
  tc2 D {{Eqb (prod lp:A lp:B)}} {{@eqP lp:A lp:B lp:EqA lp:EqB}} :-
    coq.say D "Found eqP with two holes : ?EqA and ?EqB",
    D1 is D + 1,
    tc2 D1 {{Eqb lp:A}} EqA, 
    tc2 D1 {{Eqb lp:B}} EqB,
    coq.say D "Solved EqA:" {coq.term->string EqA} "and EqB:" {coq.term->string  EqB}.
}}.
Elpi Typecheck TC_solver.

(* Without the following line we run the coq solver *)
Elpi Override TC TC_solver Only Eqb.
(* Check (@eqP unit bool _ _ eqU eqB). *)

Set Printing All.
Goal (eqb (tt, (tt, true)) (tt, (tt, true))) = true. easy. Qed.