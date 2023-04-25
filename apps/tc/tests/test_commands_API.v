From elpi.apps Require Import compiler.
From elpi.apps.tc.tests Require Import eqSimplDef.

Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  pred count i:gref, i:int.
  count GR Len :-
    if (const _ = GR)
      (std.findall (instance _ _ GR) Cl,
      std.assert! ({std.length Cl} = Len) 
      "Unexpected number of instances")
      true. 

  main [str E, int Len] :-
    coq.locate E GR,
    count GR Len.
}}.
Elpi Typecheck.

Section test1.
  Elpi AddInstances Eqb ignoreInstances eqP.
  Elpi len_test Eqb 2.
End test1.

Reset test1.

Section test2.
  Elpi len_test Eqb 0.
End test2.

Reset test2.

Section test3.
  Elpi AddInstances Eqb.
  Elpi len_test Eqb 3.
End test3.

Reset test3.

Section test4.
  Elpi AddAllInstances eqU.

  Elpi Query TC_check lp:{{
    EqP = {{:gref eqU}},
    std.assert! (not (instance _ EqP _)) "EqP should not be in the DB".
  }}.
End test4.
