(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

Declare ML Module "coq-elpi.tc".

From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
(* From elpi.apps.tc.elpi Extra Dependency "compiler.elpi" as compiler. *)
From elpi.apps.tc.elpi Extra Dependency "ho_precompile.elpi" as ho_precompile.
From elpi.apps.tc.elpi Extra Dependency "ho_compile.elpi" as ho_compile.
From elpi.apps.tc.elpi Extra Dependency "compiler1.elpi" as compiler1.
From elpi.apps.tc.elpi Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc.elpi Extra Dependency "unif.elpi" as unif.
From elpi.apps.tc.elpi Extra Dependency "ho_link.elpi" as ho_link.
From elpi.apps.tc.elpi Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc.elpi Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

From elpi.apps Require Import db.
From elpi.apps Require Export add_commands.

Set Warnings "+elpi".

Elpi Command TC.Print_instances.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  pred tc.list-printer-aux i:prop.
  tc.list-printer-aux (tc.instance _ InstGR _ Locality) :-
    coq.say InstGR "with locality" Locality.

  pred tc.list-printer i:gref, i:list prop.
  tc.list-printer _ [].
  tc.list-printer ClassGR Instances :- 
    coq.say "Instances list for" ClassGR "is:",
    std.forall Instances tc.list-printer-aux. 

  main [str Class] :-
    std.assert! (coq.locate Class ClassGR) "The entered TC not exists",
    std.findall (tc.instance _ _ ClassGR _) Rules,
    tc.list-printer ClassGR Rules. 
  main [] :-
    std.forall {coq.TC.db-tc} (ClassGR\ sigma Rules\
      std.findall (tc.instance _ _ ClassGR _) Rules,
      tc.list-printer ClassGR Rules
    ).  
}}.
Elpi Typecheck.

Elpi Tactic TC.Solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File unif.
Elpi Accumulate File ho_link.
(* Elpi Accumulate File compiler. *)
Elpi Accumulate File ho_precompile.
Elpi Accumulate File ho_compile.
Elpi Accumulate File compiler1.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File modes.
Elpi Accumulate File solver.
Elpi Query lp:{{
  sigma Options\ 
    tc.all-options Options,
    std.forall Options (x\ sigma L\ x L, 
      if (coq.option.available? L _) true
        (coq.option.add L (coq.option.bool ff) ff)).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  sigma Nums\ 
    std.iota 1001 Nums, 
    std.forall Nums (x\ sigma NumStr\
      NumStr is int_to_string x,
      @global! => tc.add-tc-db NumStr (before "lastHook") (tc.hook NumStr)
    )
}}.

Elpi Command TC.Compiler.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File ho_precompile.
Elpi Accumulate File ho_compile.
Elpi Accumulate File unif.
Elpi Accumulate File ho_link.
Elpi Accumulate File compiler1.
Elpi Accumulate File modes.
Elpi Accumulate lp:{{

  /* 
    Projections of a class that are coercions, are wrongly compiled:
    In the following code:
    ```coq
      Class Animal.
      Class Bird := IsAnimal :> Animal.
    ```
    The instance IsAnimal of type Bird -> Animal, is compiled before the
    predicate for Bird; hence, Bird is not recognize as a premise of IsAnimal.
    This problem is due to the order in which the registers for Instance and
    Class creation are run.
    The solution is to do the following two jobs when a class C is created:
      1: for every projection P of C, if P is a coercion, the wrongly 
        compiled instance is replaced with a `dummy` clause.
      2: the predicate for the class is created
      3: for every projection P of C, if P is a coercion, the correct
        instance is created and added to the db
  */

  shorten tc.class-coercion.{add, remove, loop-proj}.
  main [str "remove_coercions" | Proj] :- !, loop-proj remove Proj.
  main [str "add_coercions" | Proj] :- !, loop-proj add Proj.

  main [str "new_instance", str Inst, str Cl, str Locality, int Prio] :- !,
    tc.time-it _ (coq.locate Cl GRCl,
    coq.locate Inst GRInst,
    tc.add-inst GRInst GRCl Locality Prio) "Compiler for Instance".

  main [str "new_class", str Cl] :- !,
    tc.time-it tc.oTC-time-compile-class (
      coq.locate Cl GR, tc.add-class-gr tc.classic GR
    ) "Compiler for Class".

  % used to build ad-hoc instance for eta-reduction on the argument of 
  % Cl that have function type
  main [str "default_instance", str Cl] :- !,
    tc.eta-reduction-aux.main Cl.

  main A :- coq.error "Fail in TC.Compiler: not a valid input entry" A.
}}.
Elpi Typecheck.

(* Command allowing to set if a TC is deterministic. *)
Elpi Command TC.Set_deterministic.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main [str ClassStr] :- 
    coq.locate ClassStr ClassGR, 
    std.assert! (coq.TC.class? ClassGR) "Should pass the name of a type class",
    std.assert! (tc.class ClassGR PredName _ Modes) "Cannot find `class ClassGR _ _` in the db",
    std.assert! (not (tc.instance _ _ ClassGR _)) "Cannot set deterministic a class with an already existing instance",
    tc.add-tc-db _ (after "0") (tc.class ClassGR PredName tc.deterministic Modes :- !).
}}.
Elpi Typecheck.

Elpi Command TC.Get_class_info.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main [str ClassStr] :- 
    coq.locate ClassStr ClassGR, 
    tc.class ClassGR PredName SearchMode Modes,
    coq.say "[TC] For " ClassGR ":",
    coq.say "  elpi predicate :" PredName,
    coq.say "  search mode is :" SearchMode,
    coq.say "  modes are      :" Modes.
  main [str C] :- coq.error "[TC]" C "is not found in elpi db".
  main [A] :- std.assert! (str _ = A) "first argument should be a str".
  main [_|_] :- coq.error "[TC] Get_class_info accepts only one argument of type str". 
  main [] :- coq.error "[TC] Get_class_info accepts only one argument of type str". 
  main L :- coq.error "[TC] Uncaught error on input" L. 
}}.
Elpi Typecheck.

Elpi Command TC.Unfold.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  pred tc.add-unfold i:gref.
  tc.add-unfold (const C) :-
    if (tc.unfold-constant C) true
      (tc.add-tc-db _ _ (tc.unfold-constant C)).
  tc.add-unfold GR :-
    coq.error "[TC]" GR "is not a constant".
  main L :-
    ErrMsg = "[TC] TC.Unfold accepts a list of string is accepted",
    std.map L (x\r\ sigma R\ std.assert! (str R = x) ErrMsg, coq.locate R r) L',
    std.forall L' tc.add-unfold.
}}.
Elpi Typecheck.

Elpi TC Solver Register TC.Solver.
Elpi TC Solver Activate TC.Solver.
Elpi TC Solver Override TC.Solver All.

Elpi Register TC Compiler TC.Compiler.

Elpi Export TC.Print_instances.
Elpi Export TC.Solver.
Elpi Export TC.Compiler.
Elpi Export TC.Get_class_info.
Elpi Export TC.Set_deterministic.
Elpi Export TC.Unfold.

Set Warnings "elpi".

Elpi TC.AddAllClasses.
Elpi TC.AddAllInstances.