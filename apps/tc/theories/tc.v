(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

Declare ML Module "coq-elpi-tc.plugin".

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

From elpi.apps Require Import db.
From elpi.apps Require Import add_commands.

Elpi Command print_instances.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  pred list-printer i:gref, i:list prop.
  list-printer _ [].
  list-printer ClassGR Instances :- 
    std.map Instances (x\r\ x = instance _ r _) InstancesGR,
    coq.say "Instances list for" ClassGR "is:",
    std.forall InstancesGR (x\ coq.say " " x). 

  main [str Class] :-
    std.assert! (coq.locate Class ClassGR) "The entered TC not exists",
    std.findall (instance _ _ ClassGR) Rules,
    list-printer ClassGR Rules. 
  main [] :-
    std.forall {coq.TC.db-tc} (ClassGR\ sigma Rules\
      std.findall (instance _ _ ClassGR) Rules,
      list-printer ClassGR Rules
    ).  
}}.
Elpi Typecheck.

Elpi Tactic TC_solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
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

Elpi AddAllClasses.
Elpi AddAllInstances.

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
    std.assert! (class Gr PredName _) "Cannot find `class GR _ _` in the db",
    add-tc-db _ (after "0") (class Gr PredName deterministic :- !).
}}.
Elpi Typecheck.

Elpi Command get_class_info.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main [str ClassStr] :- 
    coq.locate ClassStr ClassGR, 
    class ClassGR PredName SearchMode,
    coq.say "The predicate of" ClassGR "is" PredName "and search mode is" SearchMode.
  main [str C] :- coq.error C "is not found in elpi db".
  main [A] :- std.assert! (str _ = A) true "first argument should be a str".
  main [_|_] :- coq.error "get_class_info accepts only one argument of type str". 
  main L :- coq.error "Uncaught error on input" L. 
}}.
Elpi Override TC TC_solver All.

Elpi Register TC Compiler auto_compiler.