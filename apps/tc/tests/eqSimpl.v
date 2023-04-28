From elpi.apps Require Import eqSimplDef.
From elpi.apps Require Import compiler.

Elpi Override TC TC_check Only Eqb.
Elpi AddInstances Eqb.


Elpi Query TC_check lp:{{
  coq.warning "" "" "following should fail".
}}.
(* Fail Check (fun n m : _ => eqb n m). *)

Goal (tt, (tt, true)) == (tt, (tt, true)) = true.
  easy.
Qed.

Fail Goal (1 == 2) = true.

Goal (@eqb _ eqU tt tt) = true. easy. Qed.

Goal (@eqb _ eqU tt tt) = true. easy. Qed.

(* Set Printing All.
Check (eqb (tt, (tt, true)) (tt, (tt, true))).

Check (@eqb _ _ (tt, 1) (tt, 2)). *)