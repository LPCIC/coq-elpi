From elpi Require Export elpi.

Elpi Tactic test.
Elpi Accumulate lp:{{
  solve G Gs :-
    refine {{id _}} G Gs.
}}.

(* #805 *)
Theorem test' : True.
Proof.
  elpi test. (* I get one (expected) goal of type True, corresponding to the hole in term (id _), but also a shelved goal of type True...*)
  Unshelve. (* I get two goals here, of type True. *)
  Fail 2: exact I.
  exact I.
Qed.