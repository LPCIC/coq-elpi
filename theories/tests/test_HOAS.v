From elpi Require Import elpi.

Elpi Tactic test1 lp:{{

solve _ [G] GS :- pi x\
  coq.evd.print,
  print_constraints,
  refine {{ fun w : _ => _ }} G GS.


}}.
Elpi Typecheck.

Lemma test (x : nat) : bool -> True.
Proof.

elpi test1.

Abort.