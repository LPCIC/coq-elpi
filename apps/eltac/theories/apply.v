From elpi Require Export elpi.

Elpi Tactic apply.
Elpi Accumulate lp:{{
    pred apply i:term, i:term, o:goal, o:list sealed-goal.

    apply T _ G GL :- refine T G GL, !.

    apply Term Ty G GL :-
        whd Ty [] (prod _ _ B) [],
        apply {coq.mk-app Term [Hole]} (B Hole) G GL.

    apply _ _ _ _ :- coq.ltac.fail _ "Couldn't unify type of term with goal".

    solve (goal Ctx _ _ _ [trm T] as G) GL :-
        std.assert-ok! (coq.typecheck T Ty) "Illtyped argument",
       
        apply T Ty G GL.
}}.

Tactic Notation "eltac.apply" constr(T) := elpi apply ltac_term:(T).