From elpi Require Import elpi.

Elpi Tactic test1.
Elpi Accumulate lp:[[

solve _ [G] GS :- pi x\
  coq.evd.print,
  print_constraints,
  refine {{ fun w : _ => _ }} G GS.
]].
Elpi Typecheck.

Lemma test (x : nat) : bool -> True.
Proof.

elpi test1.

Abort.

Ltac foobar x := eapply x.

(* TODO: test evar type with a binder *)

Elpi Tactic test2.
Elpi Accumulate lp:{{

solve _ [G] GS :-
  G = goal [decl T N TY | L ] X _ _,
  coq.say N,
  L => decl T N TY => pi w\ coq.ltac1.call "foobar" [T] G GLS,
  coq.say GLS, coq.say "Proof" X, print_constraints.

}}.




Lemma test  : (forall b: ( forall b : bool, b = b), True) -> True.
Proof.
intro.

elpi test2.

intro; reflexivity.
Qed.