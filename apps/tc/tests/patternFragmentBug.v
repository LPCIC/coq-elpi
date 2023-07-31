From elpi.apps Require Import compiler.

Class X (A: Type).
Class Y (A: Type).
Class Z (A: Type).

Local Instance Inst1 A: Y (A * A). Qed. 
Local Instance Inst2 A F: (forall (a: Type), Y (F a)) -> Z A. Qed.

Elpi Accumulate TC_solver lp:{{
  :after "firstHook"
  solve1 (goal Ctx _ Ty Sol _ as G) _L GL :- !,
  var Sol,
  % Add's the section's definition to the current context
  % in order to add its TC if present
  std.map {coq.env.section} (x\r\ sigma F\ coq.env.typeof (const x) F, r = (decl (global (const x)) _ F)) SectionCtx,
  ctx->clause {std.append Ctx SectionCtx} Clauses,
  % get-last Ty InstFun,
  Ty = app [global TC | _],
  coq.say Ty,
  % coq.say "Clauses" Clauses,
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

Elpi Accumulate TC_solver lp:{{
  % tc _ A _ :- fail.

  tc _ {{Z lp:A}} {{Inst2 lp:A lp:F lp:S}} :-
    F = fun _ {{Type}} F',
    S = fun _ {{Type}} S',
    pi a\ tc {{:gref Y}} {{Y lp:{{F' a}}}} (S' a).
}}.
Elpi Typecheck TC_solver.

Elpi Override TC TC_solver All.
Elpi AddAllInstances.
Unset Typeclass Resolution For Conversion.

Goal  Z bool.
intros.
(* TODO: here Elpi Trace Fails... *)
Elpi Trace Browser.

  (* Elpi Override TC TC_solver Only Z. *)
  (* Elpi Override TC - Z. *)
  apply _.
  Show Proof.
Qed.