(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi.apps Require Import db.

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc Extra Dependency "compiler1.elpi" as compiler1.
(* From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler. *)
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "ho_unif.elpi" as ho_unif.
From elpi.apps.tc Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

Set Warnings "+elpi".

Elpi Command TC.AddAllInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File ho_unif.
Elpi Accumulate File compiler1.
Elpi Accumulate File modes.
Elpi Accumulate lp:{{  
  main L :- 
    args->str-list L L1,
    std.forall {coq.TC.db-tc} (x\ add-tc-or-inst-gr [] L1 [x]).
}}.
Elpi Typecheck.

Elpi Command TC.AddInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File ho_unif.
Elpi Accumulate File compiler1.
Elpi Accumulate File modes.
Elpi Accumulate File parser_addInstances.
Elpi Accumulate lp:{{
  main Arguments :- 
    parse Arguments Res, run-command Res.
}}.
Elpi Typecheck.

Elpi Command TC.AddAllClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  % Ignore is the list of classes we do not want to add
  main IgnoreStr :-
    std.map IgnoreStr (x\r\ sigma S\ str S = x, coq.locate S r) IgnoreGR,
    std.forall {coq.TC.db-tc} (x\ if (std.mem IgnoreGR x) true (add-class-gr classic x)).
}}.
Elpi Typecheck.

Elpi Command TC.AddClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main L :-
    std.mem {attributes} (attribute "deterministic" _),
    std.forall {args->str-list L} (add-class-str deterministic).
  main L :- std.forall {args->str-list L} (add-class-str classic).
  main _ :- coq.error "This commands accepts: [classic|deterministic]? TC-names*".
}}.
Elpi Typecheck.

Elpi Command TC.AddHook.
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

Elpi Command TC.Declare.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main _ :- coq.warning "TC.Declare" {tc-warning-name} 
"This command does not fully mirror the watned behavior if the class has methods
with implicit arguments (those implicits will be neglected)", fail.
  main [indt-decl D] :- declare-class D.
  main _ :- coq.error "Argument should be an inductive type".
}}.
Elpi Typecheck.

Elpi Command TC.Pending_mode.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main M :- 
    % the "o" added at the end of M stands for the solution of the goal 
    std.append M [str "o"] M1,
    add-pending-mode {args->str-list M1}.
}}.
Elpi Typecheck.


Elpi Export TC.AddAllClasses.
Elpi Export TC.AddAllInstances.
Elpi Export TC.AddClasses.
Elpi Export TC.AddInstances.
Elpi Export TC.AddHook.
Elpi Export TC.Declare.
Elpi Export TC.Pending_mode.