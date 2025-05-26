(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi.apps.tc Require Import db.

From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc.elpi Extra Dependency "ho_precompile.elpi" as ho_precompile.
From elpi.apps.tc.elpi Extra Dependency "ho_compile.elpi" as ho_compile.
From elpi.apps.tc.elpi Extra Dependency "compiler1.elpi" as compiler1.
From elpi.apps.tc.elpi Extra Dependency "unif.elpi" as unif.
From elpi.apps.tc.elpi Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc.elpi Extra Dependency "ho_link.elpi" as ho_link.
From elpi.apps.tc.elpi Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc.elpi Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc.elpi Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

(* Set Warnings "+elpi". *)

Elpi Command TC.AddAllInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File ho_precompile.
Elpi Accumulate File unif.
Elpi Accumulate File ho_link.
Elpi Accumulate File ho_compile.
Elpi Accumulate File compiler1.
Elpi Accumulate File modes.
Elpi Accumulate lp:{{  
  main L :- 
    args->str-list L L1,
    tc.time-it _ (std.forall {coq.TC.db-tc} (x\ tc.add-tc-or-inst-gr [] L1 [x])) "TC.AddAllInstances".
}}.


Elpi Command TC.AddInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File ho_precompile.
Elpi Accumulate File ho_compile.
Elpi Accumulate File unif.
Elpi Accumulate File ho_link.
Elpi Accumulate File compiler1.
Elpi Accumulate File modes.
Elpi Accumulate File parser_addInstances.
Elpi Accumulate lp:{{
  main Arguments :- 
    tc.parse Arguments Res, tc.run-command Res.
}}.


Elpi Command TC.AddAllClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  % Ignore is the list of classes we do not want to add
  main IgnoreStr :-
    std.map IgnoreStr (x\r\ sigma S\ str S = x, coq.locate S r) IgnoreGR,
    tc.time-it _ (std.forall {coq.TC.db-tc} (x\ if (std.mem IgnoreGR x) true (tc.add-class-gr tc.classic x))) "TC.AddAllClasses".
}}.


Elpi Command TC.AddClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  pred tc.add-all-classes i:list argument , i:tc.search-mode.
  tc.add-all-classes L S :-
    tc.time-it _ (std.forall {args->str-list L} (tc.add-class-str S)) "TC.AddClasses".

  main L :-
    std.mem {attributes} (attribute "deterministic" _),
    tc.add-all-classes L tc.deterministic.
  main L :- tc.add-all-classes L tc.classic.
  main _ :- coq.error "This commands accepts: [classic|deterministic]? TC-names*".
}}.


Elpi Command TC.AddHook.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  pred tc.addHook i:grafting, i:string. 
  tc.addHook Grafting NewName :- 
    @global! => tc.add-tc-db NewName Grafting (tc.hook NewName).

  main [str "before", str OldHook, str NewHook] :-
    tc.addHook (before OldHook) NewHook. 
  
  main [str "after", str OldHook, str NewHook] :-
    tc.addHook (after OldHook) NewHook. 

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


Elpi Command TC.Declare.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main _ :- coq.warning "TC.Declare" {tc.warning-name} 
"This command does not fully mirror the watned behavior if the class has methods
with implicit arguments (those implicits will be neglected)", fail.
  main [indt-decl D] :- !, tc.declare-class D.
  main _ :- coq.error "Argument should be an inductive type".
}}.


Elpi Command TC.Pending_mode.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main M :- 
    % the "o" added at the end of M stands for the solution of the goal 
    std.append M [str "o"] M1,
    tc.add-pending-mode {args->str-list M1}.
}}.

Elpi Command TC.Pending_lettify.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main [] :- tc.lettify.add.
  main [_|_] :- coq.error "TC.Pending_lettify has 0 arguments".
}}.

Elpi Export TC.AddAllClasses.
Elpi Export TC.AddAllInstances.
Elpi Export TC.AddClasses.
Elpi Export TC.AddInstances.
Elpi Export TC.AddHook.
Elpi Export TC.Declare.
Elpi Export TC.Pending_mode.