From elpi Require Export elpi.

Elpi Tactic case.
Elpi Accumulate lp:{{

  pred mk-abstracted-goal list term, term, term, list term, list term -> term.
  mk-abstracted-goal ToAbstract Goal  _IndSort Vars _VarsTys Out :-
    std.map2 ToAbstract Vars (t\v\r\ r = copy t v) Subst,
    % Non deterministically we abstract until we obtain a well typed term
    (Subst ==> copy Goal Out),
    coq.say "trying" {coq.term->string Out},
    coq.typecheck Out _ ok.

  pred mk-empty-branches term, term, list term, list term -> term.
  mk-empty-branches _K _KTy _Vars _VarsTys HOLE_.

  solve (goal _ _ GTy _ [trm T] as G) NG :- !, std.do! [
    std.assert-ok! (coq.typecheck T Ty) "input term illtyped",
    std.assert! (coq.safe-dest-app Ty (global (indt I) _) Args) "the type is not inductive",
    coq.env.indt I _ ParamsNo _ _ _ _,
    std.drop ParamsNo Args Idxs,
    std.append Idxs [T] ToAbstract,
    coq.build-match T Ty (mk-abstracted-goal ToAbstract GTy) mk-empty-branches M,
    refine M G NG
  ].

  solve _ _ :- usage.

  usage :- coq.error "Usage: eltac.case <term>".


}}.



Tactic Notation "eltac.case" constr(T) := elpi case ltac_term:(T).
