From elpi.apps Require Import tc.
From elpi.apps.tc.tests Require Import eqSimplDef.

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  pred count i:gref, i:int.
  count GR Len :-
    if (const _ = GR)
      (std.findall (tc.instance _ _ GR _) Cl,
      std.assert! ({std.length Cl} = Len) 
      "Unexpected number of instances")
      true. 

  main [str E, int Len] :-
    coq.locate E GR,
    count GR Len.
}}.
Elpi Typecheck.

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
    std.assert! (not (instance _ EqP _)) "EqP should not be in the DB".
  }}.
End test4.