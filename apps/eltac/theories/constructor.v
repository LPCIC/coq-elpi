From elpi Require Export elpi.

Elpi Tactic constructor.
Elpi Accumulate lp:{{

  solve (goal _ _ Ty _ _ as G) GS :- std.do! [
    @ltacfail! _ =>
      std.assert! (whd Ty [] (global (indt GR)) _) "The goal is not an inductive type",
    coq.env.indt GR _ _ _ _ Ks Kt,
    std.exists2 Ks Kt (k\ t\ sigma P\
      coq.saturate t (global (indc k)) P,
    refine P G GS)
  ].

  solve _ _ :- coq.error "eltac.constructor: this should never happen".

}}.

Elpi Typecheck.

Tactic Notation "eltac.constructor" := elpi constructor.
