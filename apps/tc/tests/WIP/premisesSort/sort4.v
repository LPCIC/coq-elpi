From elpi.apps.tc.tests.premisesSort Require Import sortCode.
Elpi Debug "simple-compiler".
Set TC AddModes.

Class A (S : Type) (T : Type).
Class C (S : Type) (T : Type).
Class B (S : Type) (T : Type) `(A S T, C S T) := f : forall (x : S), x = x.

Global Hint Mode A + + : typeclass_instances.
Global Hint Mode C + + : typeclass_instances.

Global Instance A1 : A nat nat. Admitted.
Global Instance C1 : C nat nat. Admitted.
Global Instance B1 (S : Type) (T : Type) (a : A S T) (c : C S T) : B S T a c. Admitted.

Elpi AddAllClasses. 
Elpi AddAllInstances.
Elpi TC Solver Override TC.Solver All.

Elpi Accumulate tc.db lp:{{
  pred get-inout-sealed-goal i:argument_mode, i:sealed-goal, o:list term.
  get-inout-sealed-goal AMode (seal (goal _ _ (app [global GR | L]) Sol _)) Res :- 
    tc-mode GR Modes, std.append L [Sol] L',
    std.map2-filter L' Modes (t\m\r\ pr AMode _ = m, var t, r = t) Res.
  get-inout-sealed-goal out (seal (goal _ _ _ Sol _)) [Sol].
  get-inout-sealed-goal _ _ [].

  pred sort-goals i:list sealed-goal, o:list int.
  sort-goals L NL :-
    std.map-i L (i\x\r\ r = pr x i) LookupList,
    std.map L (x\r\ sigma M\ get-inout-sealed-goal in x M, r = pr x M) InputModes,
    std.map L (x\r\ sigma Output Deps\ 
      get-inout-sealed-goal out x Output,
      std.map-filter InputModes (x\r\ 
        sigma Fst Snd\ pr Fst Snd = x,
        std.exists Output (v\ std.exists Snd (v1\ occurs_var v v1)), r = Fst) Deps, % O(N^2)
      sigma Output2Nb Deps2Nb\
      std.lookup! LookupList x Output2Nb,
      std.map Deps (std.lookup! LookupList) Deps2Nb,
      r = pr Output2Nb Deps2Nb) Graph, 
    coq.toposort Graph NL.

  pred sort-sealed-goals i:list sealed-goal, o:list sealed-goal.
  sort-sealed-goals SGL SortedSGL :- 
    sort-goals SGL SGLIndexes, 
    std.map SGLIndexes (x\r\ std.nth x SGL r) SortedSGL.

  :after "firstHook" msolve L N :- !,
    sort-sealed-goals L LSort,
    coq.say LSort,
    coq.ltac.all (coq.ltac.open solve) LSort N.
  
  :after "firstHook" msolve A _ :- coq.say A, sep, fail.
}}.
Elpi Typecheck TC.Solver.

Goal 3 = 3.
  Fail apply f.
Abort.