From elpi Require Import elpi.
From Stdlib Require Import ZArith Lia.

(* we test we can call ML tactics *)

Elpi Tactic xlia.
Elpi Accumulate lp:{{
  solve G GL :- coq.ltac.call-mltac "rocq-runtime.plugins.micromega" "Lia" 0 G GL ok.
}}.
Tactic Notation "mylia" :=
  Zify.zify; elpi xlia ltac_tactic:(zchecker).

Open Scope Z.

Goal 0 = 0 :> Z.
mylia.
Qed.

From Stdlib Require Import Ring.

Ltac xx rl :=
  let G := Get_goal in
  ring_lookup (PackRing Ring_simplify) [] rl G.

Elpi Tactic test.
Elpi Accumulate lp:{{
  solve (goal C R T E []) GL :- coq.ltac.call-ltac1 "xx" (goal C R T E [trm {{ 0 + 0 }}]) GL ok.
}}.

Goal forall f, 0 = f (0 + 0) :> Z.
intro f.
elpi test.
match goal with |- 0 = f 0 => idtac end.
Abort.
