From elpi Require Import elpi.

From elpi.tests Require Import test_libobject_A.

Elpi Tactic tac.
Elpi Accumulate Db a.db.
Elpi Accumulate lp:{{
  solve _ _ :-
    a X, coq.say X.
}}.


Ltac b := elpi tac.
