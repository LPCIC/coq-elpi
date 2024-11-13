(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi.apps.tc Require Import db.

From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
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
From elpi.apps.tc.elpi Extra Dependency "att_parser.elpi" as att_parser.

Set Warnings "+elpi".

Elpi Command TC.AddAllInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
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
Elpi Typecheck.

Elpi Command TC.AddInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
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
Elpi Typecheck.

Elpi Command TC.AddAllClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File att_parser.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  % Ignore is the list of classes we do not want to add
  main IgnoreStr :-
    std.map IgnoreStr (x\r\ sigma S\ str S = x, coq.locate S r) IgnoreGR,
    tc.time-it _ (std.forall {coq.TC.db-tc} (x\ if (std.mem IgnoreGR x) true (tc.declare-class-in-elpi x))) "TC.AddAllClasses".
}}.
Elpi Typecheck.

Elpi Command TC.AddClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File att_parser.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main L :- tc.time-it _ (std.forall {args->str-list L} (tc.add-class-str)) "TC.AddClasses".
}}.
Elpi Typecheck.

Elpi Command TC.AddHook.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
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
Elpi Typecheck.

Elpi Command TC.Declare.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File att_parser.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
%   main _ :- coq.warning "TC.Declare" {tc.warning-name} 
% "This command does not fully mirror the watned behavior if the class has methods
% with implicit arguments (those implicits will be neglected)", fail.
  main [indt-decl D] :- tc.declare-class D.
  main _ :- coq.error "Argument should be an inductive type".
}}.
Elpi Typecheck.

Elpi Command TC.Pending_attributes.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File modes.
Elpi Accumulate File att_parser.
Elpi Accumulate TC.Pending_attributes lp:{{
  main [] :- tc.pending.att-add.
}}.
Elpi Typecheck.

Elpi Export TC.AddAllClasses.
Elpi Export TC.AddAllInstances.
Elpi Export TC.AddClasses.
Elpi Export TC.AddInstances.
Elpi Export TC.AddHook.
Elpi Export TC.Declare.
Elpi Export TC.Pending_attributes.