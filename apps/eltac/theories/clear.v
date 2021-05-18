From elpi Require Export elpi.

Elpi Tactic clear.
Elpi Accumulate lp:{{
  pred not-hyp i:term, i:prop, o:term.
  not-hyp X (decl Y _ Ty) Y :- not (occurs X Ty), not (X = Y).
  not-hyp X (def Y _ Ty Bo) Y :- not (occurs X Ty ; occurs X Bo), not (X = Y).

  solve [trm X] (goal Ctx R T E I) [seal (goal Ctx R T E I)] :- name X, !, std.do! [
    std.map-filter Ctx (not-hyp X) Visible,
    prune E1 Visible,
    std.assert-ok! (coq.typecheck E1 T) "cannot clear",
    E = E1
  ].
  solve Args _ _ :- coq.error "clear expects 1 name, you passed:" Args.
}}.
Elpi Typecheck.
Tactic Notation "eltac.clear" constr(V) := elpi clear (V).
