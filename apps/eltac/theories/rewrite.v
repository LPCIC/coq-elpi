From elpi Require Export elpi.

Elpi Tactic rewrite.
Elpi Accumulate lp:{{
    % Second argument is a type of the form forall x1 x2 x3... P = Q.
    % First argument is a term of that type.
    % This tactic finds a subterm of the goal that Q unifies with
    % and rewrites all instances of that subterm from right to left.
    pred nested_forall i:term, i:term, o:goal, o:list sealed-goal.

    % The copy predicate used below is discussed in the tutorial here:
    % https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html#let-s-code-set-in-elpi

    nested_forall Eqpf {{@eq lp:S lp:P lp:Q }} (goal _ _ GoalType _ _ as G) GL :- 
    % First, introduce a rule that causes "copy" to act as a function
    % sending a type T to the same type, but with all 
    % subterms of T unifiable with Q to be replaced with a fresh constant x.
        pi x\ (pi J\ copy J x :- coq.unify-leq Q J ok) =>
        % Apply this copy function to the goal type.
            (copy GoalType (A x),
        % If the subterm Q did indeed appear in the goal,
        % then pattern match on the given equality assumption P = Q,
        % causing Q to be replaced with P everywhere.
            if (occurs x (A x))
            (refine (match
                Eqpf 
                (fun _ S (a\
                   fun _ {{ @eq lp:S lp:P lp:Q }} (_\ A a )
                   ))
                % We only want to create one hole,
                % the one corresponding to the 
                % contents of the (single) branch of the match.
                [Hole_])
                G GL 
            )
            (coq.ltac.fail _ "Couldn't unify.")).

    solve (goal Ctx _ _ _ [trm Eq] as G) GL :- (
        % Eq is a direct Gallina term or a gref and we will infer its type
        % from context
        coq.typecheck Eq Ty ok;
        % Eq is a reference to a declared variable in the context
        std.mem Ctx (decl Eq _ Ty)),
        coq.saturate Ty Eq Eq',
        coq.typecheck Eq' Ty' ok,
        nested_forall Eq' Ty' G GL.
}}.

Tactic Notation "eltac.rewrite" ident(T) := elpi rewrite ltac_term:(T).
Tactic Notation "eltac.rewrite" uconstr(T) := elpi rewrite ltac_term:(T).