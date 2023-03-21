From elpi Require Import elpi.
From elpi.tc Require Import instances_db.

Elpi Command add_inst_by_path.

Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{

  % takes a tc-instance and return the gref
  pred inst->gref i:tc-instance, o:gref.
  inst->gref Inst Res :-  
    tc-instance Res _ = Inst.

  % takes a Path and a GR and returns if 
  % the GR is located in Path
  pred is-in-path i:string, i:gref. 
  is-in-path Path GR :- 
    std.mem {coq.gref->path GR} Path.
  
  pred add-inst->db i:gref.
  add-inst->db Inst :-
    coq.env.typeof Inst Ty,
    coq.say Inst,
    coq.elpi.accumulate _ "tc.db" (clause _ _ (tc Ty (global Inst))).

  % Look for the instances of ClassName 
  % that are located in Path. The results are 
  % added to tc.db
  % pred find-tc i:string, i:string, i:string, i:(term -> term -> prop).
  pred find-tc i:string, i:string.
  find-tc ClassName Path :-
    coq.TC.db-for {coq.locate ClassName} Inst,
    std.map Inst inst->gref GRL,
    std.filter GRL (is-in-path Path) InstInPath,
    std.forall InstInPath add-inst->db.

  main [str ClassName, str Path]:- find-tc ClassName Path.
}}.
Elpi Typecheck.