(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

Declare ML Module "coq-elpi.tc".

From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc.elpi Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc.elpi Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc.elpi Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

From elpi.apps Require Import db.
From elpi.apps Require Export add_commands.

Elpi Command TC.Print_instances.
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

Elpi Tactic TC.Solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File compiler.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File solver.
Elpi Query lp:{{
  sigma Options\ 
    all-options Options,
    std.forall Options (x\ sigma L\ x L,
      if (coq.option.available? L _)
         true
         (coq.option.add L (coq.option.bool ff) ff)).
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

Elpi Command TC.Compiler.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
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

  main A :- coq.error "Fail in TC.Compiler: not a valid input entry" A.
}}.
Elpi Typecheck.

(* Command allowing to set if a TC is deterministic. *)
Elpi Command TC.Set_deterministic.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main [str ClassStr] :- 
    coq.locate ClassStr ClassGR, 
    std.assert! (coq.TC.class? ClassGR) "Should pass the name of a type class",
    std.assert! (class ClassGR PredName _) "Cannot find `class ClassGR _ _` in the db",
    std.assert! (not (instance _ _ ClassGR)) "Cannot set deterministic a class with more than one instance",
    add-tc-db _ (after "0") (class ClassGR PredName deterministic :- !).
}}.
Elpi Typecheck.

Elpi Command TC.Get_class_info.
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
Elpi Override TC TC.Solver All.

Elpi Register TC Compiler TC.Compiler.

Elpi Export TC.Print_instances.
Elpi Export TC.Solver.
Elpi Export TC.Compiler.
Elpi Export TC.Get_class_info.
Elpi Export TC.Set_deterministic.

Elpi TC.AddAllClasses.
Elpi TC.AddAllInstances.