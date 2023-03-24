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
  inst->gref (tc-instance Res _) Res.

  pred has-class i:term.
  has-class (app [global T|_]) :- coq.TC.class? T. 
  
  pred compile i:term, i:term, i:list prop, i:list term, o:prop.
  compile (prod _ T F) I ListRHS ListVar (pi x\ C x) :-
    pi p\ sigma L\
      if (has-class T) (L = [tc T p | ListRHS]) (L = ListRHS),
      compile (F p) I L [p | ListVar] (C p).
  compile Ty I ListRHS ListVar (tc Ty AppInst :- RevRHS) :- 
    AppInst = app [I | {std.rev ListVar}],
    std.rev ListRHS RevRHS.

  pred add-inst->db i:gref.
  :if "debug"
  add-inst->db Inst :- coq.say "Adding instance:" Inst, fail.
  add-inst->db Inst :-
    coq.env.typeof Inst Ty,
    compile Ty (global Inst) [] [] C,
    coq.elpi.accumulate _ "tc.db" (clause _ _ C).
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  pred add-modes-list i:term, i:term, i:list (list hint-mode), i:list (list term), o:prop.
  add-modes-list T (prod _ _ X) HintModes L (pi x\ C x):-
    std.map HintModes (x\r\ [r|_] = x) FST,
    std.map HintModes (x\r\ [_|r] = x) LAST,
    pi x\ sigma NewL\
      std.map2 L FST (l\m\r\ if (m = mode-input) (r = [x | l]) (r = l)) NewL,
      add-modes-list {coq.mk-app T [x]} (X x) LAST NewL (C x).
  add-modes-list T _ _ L NewTc :-
    NewTc = (pi s\ tc T s :- not (std.exists L (x\ not (std.exists x var))), !, coq.error "Invalid mode for" T).
}}.
Elpi Typecheck.

(* Hint modes added to DB *)
Elpi Accumulate lp:{{
  pred make-last-hint-mode-input i:term, o:list hint-mode.
  make-last-hint-mode-input (prod _ _ (x\ (prod _ _ _) as T)) [mode-output | L] :-
    pi x\ make-last-hint-mode-input (T x) L. 
  make-last-hint-mode-input (prod _ _ _) [mode-input].

  pred build-empty-list i:list B, o:list (list A).
  build-empty-list [] [].
  build-empty-list [_ | TL] [[] | L] :- 
    build-empty-list TL L.

  pred add-modes i:string.
  add-modes ClassName :-
    coq.locate ClassName GR,
    coq.env.typeof GR Ty,
    XX = global GR,
    coq.hints.modes GR "typeclass_instances" ModesProv,
    if (ModesProv = []) (Modes = [{make-last-hint-mode-input Ty}]) (Modes = ModesProv),
    add-modes-list XX Ty Modes {build-empty-list Modes} R,
    coq.elpi.accumulate _ "tc.db" (clause _ (before "hintHook") R).
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  pred add-class-instances i:string.
  add-class-instances ClassName :-
    add-modes ClassName,
    get-inst-by-tc-name ClassName InstL,
    std.forall InstL add-inst->db.
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  % takes a Path and a GR and returns if 
  % the GR is located in Path
  pred is-in-path i:string, i:gref. 
  is-in-path Path GR :- 
    std.mem {coq.gref->path GR} Path.

  % Look for the instances of ClassName 
  % that are located in Path.
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
    std.forall ClassNames add-class-instances.
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
