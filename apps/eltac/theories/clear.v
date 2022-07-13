From elpi Require Export elpi.

Elpi Tactic clear.
Elpi Accumulate lp:{{
  pred not-hyp i:term, i:prop, o:term.
  not-hyp X (decl Y _ Ty) Y :- not (occurs X Ty), not (X = Y).
  not-hyp X (def Y _ Ty Bo) Y :- not (occurs X Ty ; occurs X Bo), not (X = Y).

  solve (goal Ctx R T E [trm X]) [seal (goal Ctx R T E [])] :- name X, !, std.do! [
    std.map-filter Ctx (not-hyp X) VisibleRev,
    prune E1 {std.rev VisibleRev}, % preserve the order
    std.assert-ok! (coq.typecheck E1 T) "cannot clear",
    E = E1
  ].
  solve (goal _ _ _ _ Args) _ :- coq.error "clear expects 1 name, you passed:" Args.
}}.
Elpi Typecheck.
Tactic Notation "eltac.clear" hyp(V) := elpi clear ltac_term:(V).

Elpi Tactic clearbody.
Elpi Accumulate lp:{{
  pred drop-body i:list argument, i:prop, o:prop.
  drop-body ToBeCleared (def V Name Ty _Bo) (decl V Name Ty) :- std.mem ToBeCleared (trm V), !.
  drop-body _ (decl _ _ _ as X) X.
  drop-body _ (def _ _ _ _ as X) X.

  msolve [nabla G] [nabla G1] :- pi x\ msolve [G x] [G1 x].
  msolve [seal  (goal Ctx _ T E ToBeCleared)] [seal (goal Ctx1 _ T E1 [])] :-
    std.map Ctx (drop-body ToBeCleared) Ctx1,
    @ltacfail! 0 => % this failure can be catch by ltac
      Ctx1 => % in the new context, do...
        std.assert-ok! (coq.typecheck-ty T _) "cannot clear since the goal does not typecheck in the new context",
    Ctx1 => std.assert-ok! (coq.typecheck E1 T) "should not happen", % E1 see all the proof variables (the pi x in the nabla case) and T is OK in Ctx1
    E = E1. % we make progress by saying that the old goal/evar is solved by the new one (which has the same type thanks to the line above)
}}.
Elpi Typecheck.
Tactic Notation "eltac.clearbody" hyp_list(V) := elpi clearbody ltac_term_list:(V).
