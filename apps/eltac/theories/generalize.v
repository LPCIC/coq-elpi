From elpi Require Export elpi.

Elpi Tactic generalize.
Elpi Accumulate lp:{{
  pred occurs-hyp i:term, i:prop, o:term.
  occurs-hyp X (decl Y _ Ty) Y :- occurs X Ty.
  occurs-hyp X (def Y _ Ty Bo) Y :- occurs X Ty ; occurs X Bo.

  solve (goal Ctx _ _ _ [trm X] as G) GS :- name X, !, std.do! [
    std.map-filter Ctx (occurs-hyp X) Generalize,
    refine (app[NEW_,X|Generalize]) G GS,
  ].
  solve (goal _ _ _ _ Args) _ :- coq.error "eltac.generalize expects 1 name, you passed:" Args.
}}.
Elpi Typecheck.
Tactic Notation "eltac.generalize" constr(V) := elpi generalize (V).
