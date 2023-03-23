From elpi Require Import elpi.
From elpi.tc Require Import instances_db.

Elpi Command add_inst_by_path.

Elpi Accumulate Db tc.db.

Elpi Accumulate lp:{{
  % In this Accumulate, we have auxiliary functions
  % to add the instances into the DB

  pred get-inst-by-tc-name i:string, o:list gref.
  get-inst-by-tc-name ClassName GRL:-
    coq.TC.db-for {coq.locate ClassName} Inst,
    std.map Inst inst->gref GRL.

  % takes a tc-instance and return the gref
  pred inst->gref i:tc-instance, o:gref.
  inst->gref Inst Res :-  
    tc-instance Res _ = Inst.

  pred compile i:term, i:term, i:list prop, o:prop.

  % takes a Path and a GR and returns if 
  % the GR is located in Path
  pred is-in-path i:string, i:gref. 
  is-in-path Path GR :- 
    std.mem {coq.gref->path GR} Path.

  pred add-inst->db i:gref.
  :if "debug"
  add-inst->db Inst :- coq.say "Adding instance:" Inst, fail.
  add-inst->db Inst :-
    coq.env.typeof Inst Ty,
    compile Ty (global Inst) [] C,
    coq.say Ty C,
    coq.elpi.accumulate _ "tc.db" (clause _ _ C).
}}.
Elpi Typecheck. 

Elpi Accumulate lp:{{
  pred has-class i:term.
  has-class (app [global T|_]) :- coq.TC.class? T. 

  compile (prod _ T F) I ListRHS (pi x\ C x) :-
    pi p\ sigma L\
      if (has-class T) (L = [tc T p | ListRHS]) (L = ListRHS),
      compile (F p) (app[I, p]) L (C p).
  compile Ty I ListRHS (tc Ty I :- ListRHS).

  pred has-no-tc-dep i:term.
  has-no-tc-dep T :-
    coq.env.term-dependencies T DepSet,
    coq.gref.set.elements DepSet DepList,
    std.forall DepList (x\ not (coq.TC.class? x)).

  pred is-simpl-term i:term.
  is-simpl-term _.
  is-simpl-term (prod _ T E) :-
    has-no-tc-dep T,
    (pi x\ is-simpl-term (E x)).
  is-simpl-term (app _).

  % returns if GR is not a quantified instance
  pred is-simpl-gref i:gref. 
  is-simpl-gref GR :- 
    is-simpl-term {coq.env.typeof GR}.

  % Add tc if not quantified
  pred add-simpl i:string.
  add-simpl ClassName :-
    std.filter {get-inst-by-tc-name ClassName} (is-simpl-gref) SimplInst,
    std.forall SimplInst add-inst->db.
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  % Look for the instances of ClassName 
  % that are located in Path. The results are 
  % added to tc.db
  % pred find-tc i:string, i:string, i:string, i:(term -> term -> prop).
  pred add-path i:string, i:string.
  add-path ClassName Path :-
    std.filter {get-inst-by-tc-name ClassName} (is-in-path Path) InstInPath,
    std.forall InstInPath add-inst->db.
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{

  kind enum type.
  type all, instance  string -> enum.
  type path  string -> string -> enum.

  pred parse i:list argument, o:enum.
  parse [str ClassName] (all ClassName).
  parse [str InstName, str "instance"] (instance InstName).
  parse [str ClassName, str Path] (path ClassName Path).

  pred run-command i:enum.
  :if "debug"
  run-command A :- coq.say A, fail.
  run-command (all ClassName) :- add-simpl ClassName.
  run-command (instance InstName) :- add-inst->db {coq.locate InstName}.
  run-command (path ClassName Path):- add-path ClassName Path.

  % The main of the Command
  main Arguments :- run-command {parse Arguments}.
}}.
Elpi Typecheck.

(* From elpi.tc.stdpp Require Import inj_hardcoded. *)
From elpi Require Import elpi.
From stdpp Require Import base.
From elpi.tc.stdpp Require Import inj_fun_ex.
(* Elpi Bound Steps 1000. *)

Elpi add_inst_by_path "compose_inj" "instance".
Elpi add_inst_by_path "prod_map_inj" "instance".
Elpi add_inst_by_path "Inj" "inj_fun_ex".

Elpi Override TC TC_check.

Elpi Debug "debug".

Set Printing All.
Check (_ : Inj _ _ (compose g f)).
Check (_ : Inj _ _ (prod_map (compose f g) (compose f f))).
Check (_ : Inj _ _ _).