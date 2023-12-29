(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

From elpi.apps.tc Extra Dependency "base.elpi".
From elpi.apps.tc Extra Dependency "tc_aux.elpi".

(* 
  tc_option.db contains the set of options used by the solver of tc. 
  all the options are set to false by default
*)
Elpi Db tc_options.db lp:{{
  pred oTC-ignore-eta-reduction o:list string. 
  oTC-ignore-eta-reduction ["TC", "IgnoreEtaReduction"].

  % Time taken by only instance search (we time tc-recursive-search) 
  pred oTC-time-instance-search o:list string. 
  oTC-time-instance-search ["TC", "Time", "Instance", "Search"].

  % Time taken by the whole search in tc
  pred oTC-time o:list string.
  oTC-time ["TC", "Time"].

  % Time taken to refine the solution
  pred oTC-time-refine o:list string. 
  oTC-time-refine ["TC", "Time", "Refine"].

  pred oTC-clauseNameShortName o:list string. 
  oTC-clauseNameShortName ["TC", "NameShortPath"].

  pred oTC-debug o:list string.
  oTC-debug ["TC", "Debug"].

  pred oTC-use-pattern-fragment-compiler o:list string. 
  oTC-use-pattern-fragment-compiler ["TC", "CompilerWithPatternFragment"].

  pred all-options o:list ((list string) -> prop).
  all-options [
    oTC-ignore-eta-reduction, oTC-time-refine, oTC-time,
    oTC-clauseNameShortName, oTC-time-instance-search, oTC-debug, 
    oTC-use-pattern-fragment-compiler
  ].

  pred is-option-active i:(list string -> prop).
  is-option-active Opt :-
    Opt X, coq.option.get X (coq.option.bool tt).
}}.

Elpi Db tc.db lp:{{
  % the type of search for a typeclass
  % deterministic :- no backtrack after having found a solution/fail
  % classic       :- the classic search, if a path is failing, we backtrack
  kind search-mode type.
  type deterministic  search-mode.
  type classic        search-mode.

  % [instance Path InstGR ClassGR], ClassGR is the class implemented by InstGR
  pred instance o:list string, o:gref, o:gref.

  % [class ClassGR PredName SearchMode], for each class GR, it contains
  % the name of its predicate and its SearchMode 
  pred class o:gref, o:string, o:search-mode.

  % pred on which we graft instances in the database
  pred hook o:string.
  :name "firstHook" hook "firstHook".
  :name "lastHook" hook "lastHook".

  % the set of instances that we are not yet able to compile, 
  % in majority they use universe polimorphism
  pred banned o:gref.

  % [tc-signature TC Modes], returns for each Typeclass TC
  % its Modes
  pred tc-mode i:gref, o:list (pair argument_mode string).
}}.