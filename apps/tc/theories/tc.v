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

Elpi Command AddAllInstances_.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{  
  main L :- 
    args->str-list L L1,
    std.forall {coq.TC.db-tc} (x\ add-tc-or-inst-gr [] L1 [x]).
}}.
Elpi Typecheck.

Elpi Command AddInstances_.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File parser_addInstances.
Elpi Accumulate lp:{{
  main Arguments :- 
    parse Arguments Res, run-command Res.
}}.
Elpi Typecheck.

Elpi Command AddHook.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  pred addHook i:grafting, i:string. 
  addHook Grafting NewName :- 
    @global! => add-tc-db NewName Grafting (hook NewName).

  main [str "before", str OldHook, str NewHook] :-
    addHook (before OldHook) NewHook. 
  
  main [str "after", str OldHook, str NewHook] :-
    addHook (after OldHook) NewHook. 

  main [Graft, int OldHook, NewHook] :-
     main [Graft, str {calc (int_to_string OldHook)}, NewHook]. 

  main [Graft, OldHook, int NewHook] :-
     main [Graft, OldHook, str {calc (int_to_string NewHook)}]. 

  main _ :- 
    coq.error "Invalid call to command AddHook. A valid call looks like"
              "[ElpiAddHook Pos OldName NewName] where:"
              " - Pos is either after or before"
              " - OldName is the name of an existing hook"
              " - NewName is the name of the new hook".
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
      oTC-clauseNameShortName, oTC-time-refine, oTC-debug, oTC-addModes],
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

Elpi Command AddClasses_.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main L :-
    std.mem {attributes} (attribute "deterministic" _),
    std.forall {args->str-list L} (add-class-str deterministic).
  main L :- std.forall {args->str-list L} (add-class-str classic).
  main _ :- coq.error "This commands accepts: [classic|deterministic]? TC-names*".
}}.
Elpi Typecheck.

(* 
  Adds all classes in the db. 
*)
Elpi Command AddAllClasses_.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main _ :-
    coq.TC.db-tc TC,
    std.forall TC (add-class-gr classic).
}}.
Elpi Typecheck.

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

Elpi Override TC_Register auto_compiler.