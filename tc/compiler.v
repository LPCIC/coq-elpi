From elpi Require Import elpi.
From elpi.tc Require Import instances_db.

Elpi Command add_instances.

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

  pred has-class i:term.
  has-class (app [global T|_]) :- coq.TC.class? T. 
  
  pred compile i:term, i:term, i:list prop, o:prop.
  compile (prod _ T F) I ListRHS (pi x\ C x) :-
    pi p\ sigma L\
      if (has-class T) (L = [tc T p | ListRHS]) (L = ListRHS),
      compile (F p) {coq.mk-app I [p]} L (C p).
  compile Ty I ListRHS (tc Ty I :- Rev) :- std.rev ListRHS Rev.

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
    coq.elpi.accumulate _ "tc.db" (clause _ _ C).
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  pred add-modes-aux i:term, i:term, i:list hint-mode, i:list term, o:prop.
  add-modes-aux T (prod _ _ X) [Mode | TL] L (pi x\ C x) :-
    pi x\ sigma NewL\
    if (Mode = mode-input) (NewL = [x | L]) (NewL = L),
    add-modes-aux {coq.mk-app T [x]} (X x) TL NewL (C x).
  add-modes-aux T _ _ L NewTc :-
    NewTc = (pi s\ tc T s :- std.exists L var, !, coq.error "Invalid mode for" T).

  pred last-mode-is-not-flexible i:term, i:term, o:term, o:prop.
  last-mode-is-not-flexible T (prod _ _ X) _ (pi x\ C x) :- !,
    pi x\ last-mode-is-not-flexible {coq.mk-app T [x]} (X x) x (C x). 
  last-mode-is-not-flexible T _ LastTerm NewTc :- !,
    NewTc = (pi s\ tc T s :- [
      var LastTerm, !,  
      coq.error "Last param of " T "can't be flexible"
    ]), coq.say T.

  pred add-modes i:string.
  add-modes ClassName :-
    coq.locate ClassName GR,
    coq.env.typeof GR Ty,
    XX = global GR,
    coq.hints.modes GR "typeclass_instances" Modes,
    if2 (Modes = [])  (last-mode-is-not-flexible XX Ty _ R)
        (Modes = [_]) (std.forall Modes (x\ add-modes-aux XX Ty x [] R))
                      (coq.error "More then 1 mode is not supported"),
    coq.elpi.accumulate _ "tc.db" (clause _ (before "hook") R).
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  pred has-no-tc-dep i:term.
  has-no-tc-dep T :-
    coq.env.term-dependencies T DepSet,
    coq.gref.set.elements DepSet DepList,
    std.forall DepList (x\ not (coq.TC.class? x)).

  pred is-simpl-term i:term.
  is-simpl-term _.
  is-simpl-term (prod _ T E) :- !,
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
    add-modes ClassName,
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
  type path  string -> string -> enum.
  type instances, classes list string -> enum.
  type exclude  string -> list string -> enum.

  pred args->str-list i:list argument, o: list string.
  args->str-list L Res :-
    std.map L (x\r\ str r = x) Res.

  pred parse i:list argument, o:enum.
  parse [str "instances", str "path" | _] _ :- !, std.fatal-error "The list [instances, path | _ ] is not accepted".
  parse [str ClassName, str "path", str Path] (path ClassName Path).
  parse [str "instances" | InstNames] (instances Res) :-
    args->str-list InstNames Res.
  parse [str ClassName, str "exclude" | InstNames] (exclude ClassName Res) :-
    args->str-list InstNames Res.
  parse ClassNames (classes Res) :- args->str-list ClassNames Res.
  parse [str "classes" | ClassNames] R :- parse ClassNames R.

  pred run-command i:enum.
  :if "debug"
  run-command A :- coq.say A, fail.
  run-command (classes ClassNames) :- 
    std.forall ClassNames add-simpl.
  run-command (instances InstNames) :- 
    std.map InstNames coq.locate L,
    std.forall L add-inst->db.
  run-command (path ClassName Path):- 
    add-path ClassName Path.
  run-command (exclude ClassName InstNames):- 
    std.map InstNames coq.locate InstGR,
    std.filter 
      {get-inst-by-tc-name ClassName} 
      (x\ not (std.mem InstGR x)) 
      SimplInst,
    std.forall SimplInst add-inst->db.

  % The main of the Command
  main Arguments :- parse Arguments Res, run-command Res.
}}.
Elpi Typecheck.
