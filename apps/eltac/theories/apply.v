From elpi Require Export elpi.

Elpi Tactic apply.
Elpi Accumulate lp:{{
    pred apply i:term, i:term, o:goal, o:list sealed-goal.

    apply T _ G GL :- refine T G GL.

    apply Term (prod _ A B) G GL :-
        Hole = {{ _ }},
        coq.typecheck Hole A ok,
        whd (app [Term, Hole]) [] HD ARGS,
        unwind HD ARGS Term',
        apply Term' (B Hole) G GL.

    apply _ _ _ _ :- coq.ltac.fail _ "Couldn't unify type of term with goal".
        
    solve (goal Ctx _ _ _ [trm T] as G) GL :-
        (% T is a direct reference to a global definition or axiom
        T = global Gref, coq.env.typeof Gref Ty;
        % T is a direct Gallina term and we will infer its type
        % from context
        coq.typecheck T Ty ok;
        % Eq is a reference to a declared variable in the context
        std.mem Ctx (decl T _ Ty)),
       
        apply T Ty G GL.
}}.

Tactic Notation "eltac.apply" constr(T) := elpi apply ltac_term:(T).