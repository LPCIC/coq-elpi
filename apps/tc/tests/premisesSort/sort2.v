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
Global Instance C1 {T : Type} `{e : A T, B T} : C bool. Admitted.

Elpi Accumulate tc.db lp:{{
  pred get-inout i:argument_mode, i:term, o:list term.
  % TODO: the second arg may not be an (app L)
  get-inout AMode (app [global GR | L]) Res :- 
    std.drop-last 1 {tc-mode GR} Modes, 
    std.map2-filter L Modes (t\m\r\ pr AMode _ = m, r = t) Res.
  get-inout _ _ [].

  pred sort-hypothesis i:list term, o:list int.
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
      std.map-filter InputModes (x\r\ std.exists Output (v\ sigma Fst Snd\ 
        pr Fst Snd = x, occurs v Snd, r = Fst)) Deps, % O(N^2)
      sigma Output2Nb Deps2Nb\
      std.lookup! LookupList x Output2Nb,
      std.map Deps (std.lookup! LookupList) Deps2Nb,
      r = pr Output2Nb Deps2Nb) Graph, 
      coq.toposort Graph NL.

  pred compile-aux1 i:term, i:term, i:list term, i:list univ, i:list term, i:prop, i:prop, o:prop, o:bool.
  :name "compiler-aux:start"
  compile-aux1 Ty I [] [X | XS] [] IsPositive IsHead (pi x\ C x) IsLeaf :- !,
    pi x\ copy (sort (typ X)) (sort (typ x)) => copy Ty (Ty1 x),
      compile-aux1 (Ty1 x) I [] XS [] IsPositive IsHead (C x) IsLeaf.
  compile-aux1 (prod N T F) I ListVar [] Types IsPositive IsHead Clause ff :- !,
    (if IsPositive (Clause = pi x\ C x) (Clause = (pi x\ decl x N T => C x))),
    pi p\ sigma Type\ 
      if (app-has-class T, not (occurs p (F p))) (Type = T) (Type = app []),
      compile-aux1 (F p) I [p | ListVar] [] [Type | Types] IsPositive IsHead (C p) _.
  :if "simple-compiler"
  % TODO: here we don't do pattern fragment unification
  compile-aux1 Ty I ListVar [] Types IsPositive IsHead Clause tt :- !,
    sort-hypothesis Types TypesSortedIndexes,                         % O (n^3)
    % std.map-i Types (i\e\r\ r = i) TypesSortedIndexes,
    std.map TypesSortedIndexes (x\r\ std.nth x ListVar r) SortedVars, % O (n^2)
    std.map TypesSortedIndexes (x\r\ std.nth x Types r) SortedTypes,  % O (n^2)
    coq.mk-app I {std.rev ListVar} AppInst,
    std.map2-filter SortedTypes SortedVars (t\v\r\ 
      compile-aux1 t v [] [] [] (not IsPositive) false r _) Premises,
    make-tc IsHead Ty AppInst Premises Clause.

  :after "firstHook"
  compile-aux Ty Inst _Premises _VarAcc UnivL IsPositive IsHead Clause NoPremises :- !,
    compile-aux1 Ty Inst [] UnivL [] (IsPositive = tt, true; false) IsHead Clause NoPremises.
}}.
Elpi Typecheck AddAllInstances.

Elpi Override TC TC_solver All.
Elpi AddAllClasses. 
Elpi AddAllInstances.

Goal C bool.
  apply _.
Qed.