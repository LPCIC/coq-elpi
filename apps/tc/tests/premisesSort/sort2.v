From elpi Require Import compiler.
Elpi Debug "simple-compiler".
Set AddModes.

Class A (S : Type).
Class B (S : Type).
Class C (S : Type).

Global Hint Mode A + : typeclass_instances.

Global Instance A1 : A nat. Admitted.

Global Instance B1 : B nat. Admitted.

(* 
  Here since the output of T is input in A, we want to reorder
  the goals such that the proof of be is computed first.
  Question do we want to raise an error or try to rearrange 
  subgoals in C1. We can try to make an analysis in the compiling
  phase to raise the error.
*)
Global Instance C1 {T : Type} `{A T, B T} : C bool. Admitted.

Elpi Override TC TC_solver All.
Elpi AddAllClasses. 
Elpi AddAllInstances.

Elpi Accumulate TC_solver lp:{{
  pred get-inout i:argument_mode, i:term, o:list term.
  % TODO: the second arg may not be an (app L)
  get-inout AMode (app [global GR | L]) Res :- 
    tc-mode GR Modes', 
    std.drop-last 1 Modes' Modes, 
    std.map2-filter L Modes (t\m\r\ pr AMode _ = m, r = t) Res.
  get-inout _ (global _) [].

  pred sort-hypothesis i:list term, o:list any.
  sort-hypothesis L NL :-
    std.map-i L (i\x\r\ r = pr x i) LookupList,
    std.map L (x\r\ sigma M\ get-inout in x M, r = pr x M) InputModes,
    % foreach goal, we associate those types having a dependency on it, 
    % in particular a goal G2 depends on G1 if an input mode of G1 is in 
    % output mode of G2
    std.map L (x\r\ sigma Output Deps\ % O(N^3 * check of occurs)
      % the list of variable in input of the current goal G
      get-inout out x Output,
      % for each output modes of all goals, we keep those having an output
      % which exists in the input variable of G
      std.map-filter InputModes (x\r\ std.exists Output (var\ sigma Fst Snd\ 
        pr Fst Snd = x, occurs var Snd, r = Fst)) Deps,
      sigma Output2Nb Deps2Nb\
      std.lookup! LookupList x Output2Nb,
      std.map Deps (x\r\ std.lookup! LookupList x r) Deps2Nb,
      r = pr Output2Nb Deps2Nb) Graph, 
      coq.toposort Graph Sorted, 
      std.map Sorted (x\r\ std.nth x L r) NL.

  pred get_premises i:term, i:list term, i:list term, o:list term.
  get_premises (prod _ A B) Types Vars L :- !,
    if (is-instance-term A) (NL = [A | Types]) (NL = Types),
    pi x\ get_premises (B x) NL [x | Vars] L.
  get_premises _ T _ _ :- 
    sort-hypothesis T L,
    coq.say "The sorted res is" L.
}}.
Elpi Typecheck TC_solver.

(* Elpi Print TC_solver. *)

Elpi Query TC_solver lp:{{
  get_premises {coq.env.typeof {{:gref C1}}} [] [] _.
}}.

Elpi Accumulate TC_solver lp:{{
  :after "firstHook" msolve A _ :- coq.say A, fail.
}}.

Goal C bool.
  (* TODO: here should not fail if we reorder premises of C1 *)
  Fail apply _.
Abort.