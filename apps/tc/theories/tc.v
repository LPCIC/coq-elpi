(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

Declare ML Module "coq-elpi-tc.plugin".

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

From elpi.apps Require Import db.
From elpi.apps Require Import add_commands.

Elpi Command print_instances.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main [str TC] :-
    std.assert! (coq.locate TC TC_Gr) "The entered TC not exists",
    std.findall (instance _ _ TC_Gr) Rules,
    coq.say "Instances list for" TC_Gr "is:" Rules. 
  main [] :-
    std.findall (instance _ _ _) Rules,
    coq.say "Instances list is:" Rules.  
}}.
Elpi Typecheck. 

Elpi Tactic TC_solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File solver.
Elpi Query lp:{{
  sigma Options\ 
    Options = [oTC-ignore-eta-reduction, oTC-resolution-time, 
      oTC-clauseNameShortName, oTC-time-refine, oTC-debug, oTC-addModes,
      oTC-use-pattern-fragment-compiler],
    std.forall Options (x\ sigma Args\ x Args, 
      coq.option.add Args (coq.option.bool ff) ff).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  sigma Nums\ 
    std.iota 1001 Nums, 
    std.forall Nums (x\ sigma NumStr\
      NumStr is int_to_string x,
      @global! => add-tc-db NumStr (before "lastHook") (hook NumStr)
    )
}}.

Elpi AddAllClasses_.
Elpi AddAllInstances_.

Elpi Command auto_compiler.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{
  main [str Inst, str Cl, str Locality, int Prio] :- !,
    % coq.safe-dest-app Inst (global GRInst) _,
    % coq.safe-dest-app Cl (global GRCl) _,
    coq.locate Cl GRCl,
    coq.locate Inst GRInst,
    add-inst GRInst GRCl Locality Prio.

  main [str Cl] :- !,
    % coq.safe-dest-app Cl (global GR) _,
    coq.locate Cl GR,
    add-class-gr classic GR.

  main A :- coq.error "Fail in auto_compiler: not a valid input entry" A.
}}.
Elpi Typecheck.

(* Command allowing to set if a TC is deterministic. *)
Elpi Command set_deterministic.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main [str ClStr] :- 
    coq.locate ClStr Gr, 
    std.assert! (coq.TC.class? Gr) "Should pass the name of a type class",
    add-tc-db _ _ (classes Gr deterministic).
}}.
Elpi Typecheck.

Elpi Register TC Compiler auto_compiler.