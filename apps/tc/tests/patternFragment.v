From elpi.apps Require Import compiler.

Elpi Override TC TC_check All.

Class X (A: Type).
Class Y (A: Type).
Class Z (A: Type).

Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a: Type), Y (F a)) -> Z A. Qed.


Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  solve1 (goal Ctx _ Ty Sol _ as G) _L GL :- !,
  var Sol,
  % Add's the section's definition to the current context
  % in order to add its TC if present
  std.map {coq.env.section} (x\r\ sigma F\ coq.env.typeof (const x) F, r = (decl (global (const x)) _ F)) SectionCtx,
  ctx->clause {std.append Ctx SectionCtx} Clauses,
  get-TC-of-inst-type Ty TC,
  coq.say Ty,
  Clauses => if (tc-search-time TC Ty X) 
    (
      coq.say {coq.term->string X},
      % @no-tc! => coq.elaborate-skeleton X _ X' ok,
      % coq.say "Solution " X "end" X' "caio",
      % std.assert! (ground_term X') "solution not complete",
      my-refine X G GL; 
      coq.say "illtyped solution:" {coq.term->string X}
    ) 
    (GL = [seal G]).
}}.

Elpi Typecheck TC_check.
Elpi AddAllInstances.
(* Elpi Print TC_check. *)

Elpi Accumulate TC_check lp:{{
  tc {{:gref Z}} {{Z lp:A}} {{Inst2 lp:A lp:{{fun _ _ F}} lp:{{fun _ _ S}}}} :-
    pi a\ tc {{:gref Y}} (app [global {{:gref Y}}, F a]) (S a).

  :before "fold-map:start"
  fold-map  G V T _ :- G = app[X, _], name X, !, T = fun _ _ V.
  
}}.
Elpi Typecheck TC_check.
(* Elpi Print TC_check. *)

Elpi Query TC_check lp:{{
  A = {{:gref Inst2}},
  coq.env.typeof A Ty, 
  fold-map Ty X Ty1 _.
}}.

Goal  Z bool.
  apply _.
Qed.