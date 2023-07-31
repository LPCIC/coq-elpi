From elpi.apps Require Import compiler.
From elpi.apps.tc.tests Require Import eqSimplDef.
From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.

Elpi Debug "simple-compiler". 

Set AddModes.
Elpi AddClasses Eqb.
Elpi AddInstances Eqb.

(* 
  Tests if the modes of TC are added exactly one time 
  to the DB
*)

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  pred only-one-tc i:gref.
  only-one-tc Gr :-
    not (app-has-class {coq.env.typeof Gr}).
  only-one-tc (indt _).
  only-one-tc (const _ as GR) :-
    std.findall (classes GR _) Cl,
    std.assert! ({std.length Cl} = 1) 
    "Unexpected number of instances". 
  only-one-tc Gr :- coq.error "Should not be here" Gr.

  main [str "all_only_one"] :- !,
    std.forall {coq.TC.db-tc} only-one-tc.

  main [str E] :-
    coq.locate E GR,
    only-one-tc GR.
}}.
Elpi Typecheck.

Elpi len_test Eqb.

Elpi AddAllClasses.
Elpi AddAllInstances.

Elpi len_test "all_only_one".