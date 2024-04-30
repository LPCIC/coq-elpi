(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

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
  
  pred oTC-time-build-query o:list string. 
  oTC-time-build-query ["TC", "Time", "Build", "Query"].
  
  pred oTC-time-mode-check o:list string. 
  oTC-time-mode-check ["TC", "Time", "Mode", "Check"].

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
    oTC-use-pattern-fragment-compiler, oTC-time-build-query,
    oTC-time-mode-check
  ].

  pred is-option-active i:(list string -> prop).
  is-option-active Opt :-
    Opt X, coq.option.get X (coq.option.bool tt).

  pred tc-warning-name o:string.
  tc-warning-name "[TC] Warning".
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

  % [class ClassGR PredName SearchMode Modes], for each class GR, it contains
  % the name of its predicate and its SearchMode 
  pred class o:gref, o:string, o:search-mode, o:list string.

  % pred on which we graft instances in the database
  pred hook o:string.
  :name "firstHook" hook "firstHook".
  :name "lastHook" hook "lastHook".
  
  % [unfold-constant C] constants to be unfolded before goal resolution
  pred unfold-constant o:constant.

  % the set of instances that we are not yet able to compile, 
  % in majority they use universe polimorphism
  pred banned o:gref.

  pred pending-mode o:list string.

  pred dummy.

  pred ho-link o:term, i:term, o:A.
}}.
