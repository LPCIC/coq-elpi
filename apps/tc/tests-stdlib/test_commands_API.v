From elpi.apps Require Import tc.
From elpi_apps_tc_tests_stdlib Require Import eqSimplDef.

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  pred counti i:gref, i:int.
  counti GR Len :-
    if (const _ = GR)
      (std.findall (tc.instance _ _ GR _) Cl,
      std.assert! ({std.length Cl} = Len) 
      "Unexpected number of instances")
      true. 

  main [str E, int Len] :-
    coq.locate E GR,
    counti GR Len.
}}.


TC.AddClasses Eqb.

Module test1.
  TC.AddInstances Eqb ignoreInstances eqP.
  Elpi len_test Eqb 2.
End test1.
Reset test1.

Module test2.
  Elpi len_test Eqb 0.
End test2.
Reset test2.

Module test3.
  TC.AddInstances Eqb.
  Elpi len_test Eqb 3.
End test3.
Reset test3.


(* About RewriteRelation.

About RelationClasses.RewriteRelation.


Elpi Query TC.Solver lp:{{
  coq.gref->id {{:gref RelationClasses.RewriteRelation}} L. 
}}. *)

Module test4.
  TC.AddAllClasses.
  TC.AddAllInstances eqU.

  Elpi Query TC.Solver lp:{{
    EqP = {{:gref eqU}},
    std.assert! (not (tc.instance _ EqP _ _)) "EqP should not be in the DB".
  }}.
End test4.