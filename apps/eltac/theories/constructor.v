From elpi Require Export elpi.

Elpi Tactic constructor.
Elpi Accumulate lp:{{

  solve _ G GS :- std.do! [
    G = goal Ctx _ Ty _ _,
    @ltacfail! _ =>
      std.assert! (Ctx => whd Ty [] (global (indt GR)) _) "The goal is not an inductive type",
    coq.env.indt GR _ _ _ _ Ks Kt,
    std.exists2 Ks Kt (k\ t\ sigma P\
      Ctx => coq.saturate t (global (indc k)) P,
    refine P G GS)
  ].

  solve _ _ _ :- coq.error "eltac.constructor: this should never happen".

}}.

Elpi Typecheck.

Tactic Notation "eltac.constructor" := elpi constructor.
