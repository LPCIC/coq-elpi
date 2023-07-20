
From elpi Require Import compiler.

Elpi Accumulate tc.db lp:{{
  pred get-pattern-fragment i:term, o:list term.

  pred get-inout i:argument_mode, i:term, o:list term.
  % TODO: the second arg may not be an (app L)
  get-inout AMode (app [global GR | L]) Res :- 
    std.drop-last 1 {tc-mode GR} Modes, 
    std.map2-filter L Modes (t\m\r\ pr AMode _ = m, r = t) Res.
  get-inout _ _ [].

  % CurrentType is the type of the current instance to get its input variables,
  % These variables should not create edges in the graph
  pred sort-hypothesis i:term, i:list term, o:list int.
  sort-hypothesis (app [_ | InputCurrentType]  as CurrentType) L NL :-
    std.map-i L (i\x\r\ r = pr x i) LookupList,
    coq.say CurrentType InputCurrentType,
    std.map L (x\r\ sigma M M'\ get-inout in x M, 
      std.filter M (x\ not (std.mem InputCurrentType x)) M', 
      r = pr x M') InputModes,
    % foreach goal, we associate those goals having a dependency on it, 
    % in particular a goal G2 depends on G1 if a variable V is in 
    % output mode for G1 and in input mode for G2 (the dependency graph will
    % and edge going from G1 to G2 : G1 -> G2)
    std.map L (x\r\ sigma Output Deps\ % O(N^3 * check of occurs)
      % the list of variable in input of the current goal G
      get-inout out x Output,
      % for each output modes of all goals, we keep those having an output
      % which exists in the input variable of G
      std.map-filter InputModes (x\r\ 
        sigma Fst Snd\ pr Fst Snd = x,
        std.exists Output (v\ std.exists Snd (v1\ occurs v v1)), r = Fst) Deps, % O(N^2)
      sigma Output2Nb Deps2Nb\
      std.lookup! LookupList x Output2Nb,
      std.map Deps (std.lookup! LookupList) Deps2Nb,
      r = pr Output2Nb Deps2Nb) Graph, 
    coq.toposort Graph NL.

  pred sort-and-compile-premises i:term, i:list term, i:list term, i:prop, o:list prop. 
  sort-and-compile-premises CurrentType Types Vars IsPositive Premises :- 
    sort-hypothesis CurrentType Types TypesSortedIndexes,             % O (n^3)
    % std.map-i Types (i\e\r\ r = i) TypesSortedIndexes,
    std.map TypesSortedIndexes (x\r\ std.nth x Vars r) SortedVars,    % O (n^2)
    std.map TypesSortedIndexes (x\r\ std.nth x Types r) SortedTypes,  % O (n^2)
    std.map2-filter SortedTypes SortedVars (t\v\r\ 
      compile-aux1 t v [] [] [] (not IsPositive) false r _) Premises.

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
    sort-and-compile-premises Ty Types ListVar IsPositive Premises,
    coq.mk-app I {std.rev ListVar} AppInst,
    make-tc IsHead Ty AppInst Premises Clause.
  compile-aux1 Ty I ListVar [] Types IsPositive IsHead Clause tt :- !,
    sort-and-compile-premises Ty Types ListVar IsPositive Premises,
    coq.mk-app I {std.rev ListVar} AppInst,
    std.append {get-pattern-fragment Ty} {get-pattern-fragment AppInst} Term-to-be-fixed,
    std.fold Term-to-be-fixed 0 (e\acc\r\ sigma L X\ e = app X, std.length X L, r is acc + L - 1) Len,
    if (IsPositive) (IsPositiveBool = tt) (IsPositiveBool = ff),
    remove-ho-unification IsHead IsPositiveBool Len Ty AppInst Premises Term-to-be-fixed [] [] [] [] [] Clause.

  :after "firstHook"
  compile-aux Ty Inst _Premises _VarAcc UnivL IsPositive IsHead Clause NoPremises :- !,
    compile-aux1 Ty Inst [] UnivL [] (IsPositive = tt, true; false) IsHead Clause NoPremises.
}}.
Elpi Typecheck TC_solver.