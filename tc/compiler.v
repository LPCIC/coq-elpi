From elpi Require Import elpi.
From elpi.tc Require Import instances_db.

Elpi Command add_instances.

Set Warnings "+elpi".

Elpi Accumulate Db tc.db.

(* Auxiliary predicates *)
Elpi Accumulate lp:{{
  % returns the classes on which the current gref depends
  pred get-sub-classes i:gref, o:list gref.
  get-sub-classes GR Res :-
    coq.env.dependencies GR _ DepSet,
    coq.gref.set.elements DepSet DepList,
    std.filter DepList coq.TC.class? Res.

  % returns all the instances of the passed ClassName
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
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  % [add-inst->db IgnoreClassDepL Inst] add the Inst to
  % the database except those depending on at least one 
  % inside IgnoreClassDepL
  pred add-inst->db i:list gref, i:gref.
  :if "debug"
  add-inst->db _ Inst :- coq.say "Adding instance:" Inst, fail.
  add-inst->db IgnoreClassDepL Inst :-
    get-sub-classes Inst Dep,
    if (not (std.exists Dep (x\ std.mem IgnoreClassDepL x))) 
    (
      if ({std.length Dep} > 1) (coq.warning "TC-warning" "add-inst-with-multiple-deps" "Adding" Inst "which dependes on mulitple class dependencies:" Dep) true,
      coq.env.typeof Inst Ty,
      compile Ty (global Inst) [] [] C,
      coq.elpi.accumulate _ "tc.db" (clause _ _ C)
    ) 
    true.
}}.
Elpi Typecheck.

(* Hint modes added to DB *)
Elpi Accumulate lp:{{
  pred add-modes-aux i:term, i:term, i:list (list hint-mode), i:list (list term), o:prop.
  add-modes-aux T (prod _ _ X) HintModes L (pi x\ C x):-
    std.map HintModes (x\r\ [r|_] = x) FST,
    std.map HintModes (x\r\ [_|r] = x) LAST,
    pi x\ sigma NewL\
      std.map2 L FST (l\m\r\ if (m = mode-input) (r = [x | l]) (r = l)) NewL,
      add-modes-aux {coq.mk-app T [x]} (X x) LAST NewL (C x).
  add-modes-aux T _ _ L NewTc :-
    NewTc = (pi s\ tc T s :- not (std.exists L (x\ not (std.exists x var))), !, coq.error "Invalid mode for" T).

  % takes the type of a class and build a list
  % of hint mode where the last element is mandatory
  pred make-last-hint-mode-input i:term, o:list hint-mode.
  make-last-hint-mode-input (prod _ _ (x\ (prod _ _ _) as T)) [mode-output | L] :-
    pi x\ make-last-hint-mode-input (T x) L. 
  make-last-hint-mode-input (prod _ _ _) [mode-input].

  % build a list of the seme langht as the the passed one
  % where all the elements are []
  pred build-empty-list i:list B, o:list (list A).
  build-empty-list [] [].
  build-empty-list [_ | TL] [[] | L] :- 
    build-empty-list TL L.

  % add the hint modes of a Class to the database.
  % note that if the Class has not specified hint mode
  % then we assume the hint mode to be - - - ... !
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
  % [add-class-instances IgnoreDepClass ClassName] look
  % for all the instances of ClassName and call the pred
  % add-inst->db
  pred add-class-instances i:list string, i:string.
  add-class-instances IgnoreDepClass ClassName :-
    add-modes ClassName,
    get-inst-by-tc-name ClassName InstL,
    std.forall InstL (add-inst->db {std.map IgnoreDepClass coq.locate}).
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
    std.forall InstInPath (add-inst->db []).
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{

  kind enum type.
  type path  string -> string -> enum.
  type instances, classes list string -> enum.
  type ignoreInstances, ignoreClasses  string -> list string -> enum.

  pred args->str-list i:list argument, o: list string.
  args->str-list L Res :-
    std.map L (x\r\ str r = x) Res.

  pred parse i:list argument, o:enum.
  parse [str "instances", str "path" | _] _ :- !, std.fatal-error "The list [instances, path | _ ] is not accepted".
  parse [str ClassName, str "path", str Path] (path ClassName Path).
  parse [str "instances" | InstNames] (instances Res) :-
    args->str-list InstNames Res.
  parse [str ClassName, str "ignoreInstances" | InstNames] (ignoreInstances ClassName Res) :-
    args->str-list InstNames Res.
  parse [str ClassName, str "ignoreClasses" | ClassNames] (ignoreClasses ClassName Res) :-
    args->str-list ClassNames Res.
  parse ClassNames (classes Res) :- args->str-list ClassNames Res.
  parse [str "classes" | ClassNames] R :- parse ClassNames R.

  pred run-command i:enum.
  :if "debug"
  run-command A :- coq.say A, fail.
  run-command (classes ClassNames) :- 
    std.forall ClassNames (add-class-instances []).
  run-command (ignoreClasses ClassName IgnoreInstances) :- 
    add-class-instances IgnoreInstances ClassName.
  run-command (instances InstNames) :- 
    std.map InstNames coq.locate L,
    std.forall L (add-inst->db []).
  run-command (path ClassName Path):- 
    add-path ClassName Path.
  run-command (ignoreInstances ClassName InstNames):- 
    std.map InstNames coq.locate InstGR,
    std.filter 
      {get-inst-by-tc-name ClassName} 
      (x\ not (std.mem InstGR x)) 
      SimplInst,
    std.forall SimplInst (add-inst->db []).

  % The main of the Command
  main Arguments :- parse Arguments Res, run-command Res.
}}.
Elpi Typecheck.
