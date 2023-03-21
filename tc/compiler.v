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

  % returns if GR is not a quantified instance
  pred is-simpl i:gref. 
  is-simpl GR :- 
    coq.env.typeof GR (app _).

  pred add-inst->db i:gref.
  :if "get added classes"
  add-inst->db Inst :- coq.say Inst.

  add-inst->db Inst :-
    coq.env.typeof Inst Ty,
    coq.elpi.accumulate _ "tc.db" (clause _ _ (tc Ty (global Inst))).

  pred get-inst-by-tc-name i:string, o:list gref.
  get-inst-by-tc-name ClassName GRL:-
    coq.TC.db-for {coq.locate ClassName} Inst,
    std.map Inst inst->gref GRL.

  % Look for the instances of ClassName 
  % that are located in Path. The results are 
  % added to tc.db
  % pred find-tc i:string, i:string, i:string, i:(term -> term -> prop).
  pred add-path i:string, i:string.
  add-path ClassName Path :-
    std.filter {get-inst-by-tc-name ClassName} (is-in-path Path) InstInPath,
    std.forall InstInPath add-inst->db.

  % Add tc if not quantified
  pred add-simpl i:string.
  add-simpl ClassName :-
    std.filter {get-inst-by-tc-name ClassName} (is-simpl) InstInPath,
    std.forall InstInPath add-inst->db.

  main [str ClassName, str ""] :- !, add-simpl ClassName.
  main [str ClassName, str Path]:- add-path ClassName Path.
}}.
Elpi Typecheck.
