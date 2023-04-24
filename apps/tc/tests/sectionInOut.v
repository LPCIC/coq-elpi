From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps Require Import compiler.

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate lp:{{
  main [int Len] :-
    std.findall (instance _ _ _) Insts,
    std.map Insts (x\r\ instance _ r _ = x) R,
    % coq.say R,
    std.assert! ({std.length R} = Len) 
      "Unexpected number of instances",
    std.forall R (x\ sigma L\
      std.assert! (count R x L, L = 1) "Duplicates in instances"). 
}}.
Elpi Typecheck.

Class Eqb A:= eqb: A -> A -> bool.
Global Instance eqA : Eqb unit := { eqb x y := true }.

Elpi add_instances Eqb.

Elpi len_test 1.

Section A.
  Context (A : Type).
  Global Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
  Elpi add_instances Eqb.
  Elpi len_test 2.
  
  Global Instance eqC : Eqb A := {eqb _ _ := true}.
  Elpi add_instances Eqb.
  Elpi len_test 3.

  Section B.
    Context (B : Type).
    Global Instance eqD : Eqb B := {eqb _ _ := true}.
    Elpi add_instances Eqb.
    Elpi len_test 4.
  MySectionEnd.

  Elpi len_test 4.

MySectionEnd.

(* 
  TODO : the order is not mantained - 
  the list of instances is A B D C and not A B C D.
  Uncomment line 11 to see this behavior
*)
Elpi len_test 4.



