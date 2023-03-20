From elpi Require Import elpi.
From elpi.tc.stdpp Require Import inj_hardcoded.

Elpi Command compiler_simpl_instances.
Elpi Accumulate lp:{{

  % takes a tc-instance and return the gref on the form of a term
  pred inst-to-term i:tc-instance, o:term.
  inst-to-term INST RES :- 
    tc-instance TMP _ = INST, 
    RES = global TMP.

  % takes a tc-instance and returns if 
  % an instance is inside the wanted path
  pred is_in_path i:string, i:term. 
  is_in_path PATH TERM :- 
    global TMP = TERM, 
    coq.gref->path TMP P, 
    std.mem P PATH.

  % Look for the instances of ClassName 
  % that are located in Path. The results are 
  % added to DB
  % pred find-tc i:string, i:string, i:string, i:(term -> term -> prop).
  pred find-tc i:string, i:string, i:string.
  find-tc ClassName Path DB :-
    coq.TC.db-for {coq.locate ClassName} F,
    std.map F inst-to-term GR,
    std.filter GR (is_in_path Path) INST,
    std.forall INST (x\
      coq.typecheck x Ty ok,
      coq.elpi.accumulate _ DB (clause _ _ (tc Ty x))
    ).

  main [str ClassName, str Path, str DB]:- find-tc ClassName Path DB.
}}.
Elpi Typecheck.