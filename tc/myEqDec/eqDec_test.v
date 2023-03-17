(* Require Export Bool Arith List.
Import ListNotations. *)
From elpi.tc Require Import eqDec_proof.
From elpi Require Import elpi.

Set Printing Implicit.
Print eq_nat.
Print eq_bool.
Print eq_list.
Unset Printing Implicit.
Set Printing All.
Print EqDec.
Unset Printing All.

Check (eq_nat : EqDec nat).

Elpi Command print_db.
Elpi Accumulate lp:{{
  main [] :- std.findall (eqDec _ _ _) L, !, coq.say "The Db contains" L.
}}.

Elpi Query lp:{{
  coq.locate "EqDec" A.
}}.

Compute (nil == nil).
Compute ([2; 1] == [1]).
Compute ([true; true] == [true]).

Compute (3 == 4).
Compute (true == false).
Compute (eqb 3 3).
Check (N 3 L).



Check (L == L).
Compute (L1 == L1).
Compute (N1 5 L (N false L L) == N1 5 L (N false L (N true L L))).


Compute (LA (LB 4) == LA (LB 3)).

About eq_ind.
