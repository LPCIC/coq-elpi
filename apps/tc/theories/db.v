(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

(* 
  tc_option.db contains the set of options used by the solver of tc. 
  all the options are set to false by default
*)
Elpi Db tc_options.db lp:{{
  namespace tc {
    pred oTC-eta-reduce-proof o:list string. 
    oTC-eta-reduce-proof ["TC", "Eta", "Reduce", "Proof"].
  
    % Time taken by only instance search (we time tc-recursive-search) 
    pred oTC-time-instance-search o:list string. 
    oTC-time-instance-search ["TC", "Time", "Instance", "Search"].
    
    pred oTC-time-compile-goal o:list string. 
    oTC-time-compile-goal ["TC", "Time", "Compile", "Query"].
    
    pred oTC-time-mode-check o:list string. 
    oTC-time-mode-check ["TC", "Time", "Mode", "Check"].

    % Time taken by the whole search in tc
    pred oTC-time-msolve o:list string.
    oTC-time-msolve ["TC", "Time"].

    % Time taken to refine the solution
    pred oTC-time-refine o:list string. 
    oTC-time-refine ["TC", "Time", "Refine"].

    pred oTC-time-compile-instance o:list string. 
    oTC-time-compile-instance ["TC", "Time", "Compile", "Instance"].

    pred oTC-time-compile-class o:list string. 
    oTC-time-compile-class ["TC", "Time", "Compile", "Class"].

    pred oTC-clauseNameShortName o:list string. 
    oTC-clauseNameShortName ["TC", "NameShortPath"].

    pred oTC-debug o:list string.
    oTC-debug ["TC", "Debug"].

    pred oTC-use-pattern-fragment-compiler o:list string. 
    oTC-use-pattern-fragment-compiler ["TC", "CompilerWithPatternFragment"].

    pred all-options o:list ((list string) -> prop).
    all-options [
      oTC-eta-reduce-proof, oTC-time-refine, oTC-time-msolve,
      oTC-clauseNameShortName, oTC-time-instance-search, oTC-debug, 
      oTC-use-pattern-fragment-compiler, oTC-time-compile-goal,
      oTC-time-mode-check, oTC-time-compile-instance, 
      oTC-time-compile-class
    ].

    func is-option-active (func (list string) ->) ->.
    is-option-active uvar :- !, fail.
    is-option-active Opt :-
      Opt X, coq.option.get X (coq.option.bool tt).

    pred warning-name o:string.
    warning-name "[TC] Warning".
  }
}}.

Elpi Db tc.db lp:{{
  namespace tc {
    % the type of search for a typeclass
    % deterministic :- no backtrack after having found a solution/fail
    % classic       :- the classic search, if a path is failing, we backtrack
    kind search-mode type.
    type deterministic  search-mode.
    type classic        search-mode.

    % [instance Path InstGR ClassGR Locality], ClassGR is the class implemented by InstGR
    % Locality is either the empty list, or [@local!], or [@global!]
    pred instance o:list string, o:gref, o:gref, o:list prop.

    % [class ClassGR PredName SearchMode Modes], for each class GR, it contains
    % the name of its predicate and its SearchMode 
    :index (5)
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

    pred ho-link o:term, i:term, o:A.
    func link.eta term, term ->.
    func link.llam term, term ->.

  }
}}.
From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
#[superglobal] Elpi Accumulate tc.db File base.
