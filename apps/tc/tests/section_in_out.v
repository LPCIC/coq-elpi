From elpi.apps Require Import tc.
From elpi.apps.tc Extra Dependency "base.elpi" as base.

Elpi Accumulate tc.db lp:{{
  pred origial_tc o:int. 
}}.

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate lp:{{
  % contains the number of instances that are not 
  % imported from other files
  main [int Len] :-
    std.findall (instance _ _ _) Insts,
    std.map Insts (x\r\ instance _ r _ = x) R,
    WantedLength is {origial_tc} + Len,
    std.assert! ({std.length R} = WantedLength) 
      "Unexpected number of instances",
    std.forall R (x\ sigma L\
      std.assert! (count R x L, L = 1) "Duplicates in instances"). 
}}.

Elpi Query TC_solver lp:{{
  std.findall (instance _ _ _) Rules,
  std.length Rules Len,
  coq.elpi.accumulate _ "tc.db" (clause _ _ (origial_tc Len)).
}}.

Class Eqb A:= eqb: A -> A -> bool.
Global Instance eqA : Eqb unit := { eqb x y := true }.

Elpi AddAllClasses.
Elpi AddInstances Eqb.

Elpi len_test 1.

Section A.
  Context (A : Type).
  Global Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
  Elpi AddInstances Eqb.
  Elpi len_test 2.
  
  Global Instance eqC : Eqb A := {eqb _ _ := true}.
  Elpi AddInstances Eqb.
  Elpi len_test 3.

  Section B.
    Context (B : Type).
    Global Instance eqD : Eqb B := {eqb _ _ := true}.
    Elpi AddInstances Eqb.
    Elpi len_test 4.
  MySectionEnd.

  Elpi len_test 4.

MySectionEnd.

Elpi len_test 4.



