From elpi.apps Require Import compiler.
From elpi.apps.tc.tests Require Import eqSimpl.

(* 
  Tests if the modes of TC are added exactly one time 
  to the DB
*)

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  pred only-one-tc i:gref.
  only-one-tc GR :-
    if (const _ = GR)
      (std.findall (type-classes GR) Cl,
      std.assert! ({std.length Cl} = 1) 
      "Unexpected number of instances")
      true. 

  main [str "all_only_one"] :-
    std.forall {coq.TC.db-tc} only-one-tc.

  main [str E] :-
    coq.locate E GR,
    only-one-tc GR.
}}.
Elpi Typecheck.

Elpi len_test Eqb.

Elpi AddAllInstances.

Elpi len_test "all_only_one".