(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi.apps Require Import db.

From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

Elpi Command TC.AddAllInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{  
  main L :- 
    args->str-list L L1,
    std.forall {coq.TC.db-tc} (x\ add-tc-or-inst-gr [] L1 [x]).
}}.
Elpi Typecheck.

Elpi Command TC.AddInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File parser_addInstances.
Elpi Accumulate lp:{{
  main Arguments :- 
    parse Arguments Res, run-command Res.
}}.
Elpi Typecheck.

Elpi Command TC.AddAllClasses.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
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
Elpi Accumulate lp:{{
  accumulate elpi/tc_aux.
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
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate lp:{{
  main [indt-decl D] :- declare-class D.
  main _ :- coq.error "Argument should be an inductive type".
}}.
Elpi Typecheck.

Elpi Export TC.AddAllClasses.
Elpi Export TC.AddAllInstances.
Elpi Export TC.AddClasses.
Elpi Export TC.AddInstances.
Elpi Export TC.AddHook.
Elpi Export TC.Declare.