From elpi Require Export elpi.

Elpi Tactic intro.
Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [str ID] as G) GS :- !,
    coq.id->name ID N,
    refine (fun N _ _) G GS.

  solve _ _ :- usage.
  
  usage :- coq.error "Usage: eltac.intro".

}}.

Elpi Typecheck.

Tactic Notation "eltac.intro" string(ID) := elpi intro ltac_string:(ID).
Tactic Notation "eltac.intro" ident(ID) := elpi intro ltac_string:(ID).
