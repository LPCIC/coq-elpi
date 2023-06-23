From elpi Require Import elpi.

Elpi Db tc.db lp:{{
  pred classes i:gref.

  pred bool->mode-term i:bool, o:string.
  bool->mode-term tt "i:term".
  bool->mode-term ff "o:term".

  pred modes->string i:list bool, o:string.
  modes->string L S :-
    std.map L bool->mode-term L',
    std.string.concat "," L' S.

  pred list-init i:int, i:(int -> A -> prop), o:list A.
  list-init N _ _ :- N < 0, std.fatal-error "list-init negative length".
  list-init 0 _ [] :- !.
  list-init N F [A | TL] :-
    F N A, N1 is N - 1, list-init N1 F TL.

  pred fail->bool i:prop, o:bool.
  fail->bool P ff :- P, !.
  fail->bool _ tt.

  pred make-tc-modes i:int, o:string.
  make-tc-modes NB_args ModesStr :-
    list-init NB_args (x\r\ fail->bool (x = 1) r) ModesBool,
    modes->string ModesBool ModesStr.

  pred split-dot i:string, o:list string.
  split-dot S R :- rex.split "\." S R.

  pred split-dot-last i:string, o:string.
  split-dot-last S R :- std.last {split-dot S} R.

  pred gref->string-no-path i:gref, o:string.
  gref->string-no-path Gr S :-
    coq.gref->string Gr Str, split-dot-last Str S',
    S is "tc-" ^ S'.

  pred add-tc-pred i:gref, i:int.
  add-tc-pred Gr NbArgs :-
    not (classes Gr),
    make-tc-modes NbArgs Modes, 
    gref->string-no-path Gr GrStr,
    D is "pred " ^ GrStr ^ " " ^ Modes ^ ".",
    coq.elpi.add-predicate "tc.db" D,
    coq.elpi.accumulate _ "tc.db" (clause _ _ (classes Gr)).
  add-tc-pred _ _.

  pred tc i:gref, i:term, o:term. 
  pred make-tc i:term, i:term, i:list prop, o:prop.
  make-tc Ty Inst Hyp Clause :-
    app [global TC | TL] = Ty,
    gref->string-no-path TC TC_Str,
    std.append TL [Inst] Args, 
    std.length Args ArgsLen,
    add-tc-pred TC ArgsLen,
    coq.elpi.predicate TC_Str Args Q,
    Clause = (Q :- Hyp).

  pred app-has-class i:term, o:gref.
  app-has-class (prod _ _ T) C :- pi x\ app-has-class (T x) C.
  app-has-class (app [global T|_]) T :- coq.TC.class? T. 

  pred compile i:term, i:term, i:list prop, i:list term, o:prop.
  compile (prod _ T F) I ListRHS ListVar (pi x\ C x) :- !,
    pi p cond\ sigma Clause L\ 
      if (app-has-class T _) (compile T p [] [] Clause, L = [Clause | ListRHS]) (L = ListRHS),
      compile (F p) I L [p | ListVar] (C p).
  compile Ty I Premises ListVar Clause :- !,
    std.rev Premises PremisesRev,
    coq.mk-app I {std.rev ListVar} AppInst,
    make-tc Ty AppInst PremisesRev Clause.
}}.

Elpi Command addClass.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main [str TC_Name] :-  
    coq.locate TC_Name TC_Gr,
    coq.env.typeof TC_Gr TC_Ty,
    coq.count-prods TC_Ty N',
    N is N' + 1, % Plus one for the solution
    add-tc-pred TC_Gr N.
}}.
Elpi Typecheck.

Elpi Command compile.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main [str InstName] :-
    coq.locate InstName InstGr,
    coq.env.typeof InstGr InstTy,
    compile InstTy (global InstGr) [] [] Cl,
    coq.say Cl,
    coq.elpi.accumulate _ "tc.db" (clause _ _ Cl).
}}.
Elpi Typecheck.

Elpi Tactic solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  msolve L N :- !,
    coq.ltac.all (coq.ltac.open solve) {std.rev L} N.

  solve (goal _ _ Ty Sol _ as G) GL :-
    var Sol,
    Ty = app [global TC | TL'],
    std.append TL' [X] TL,
    if (coq.elpi.predicate {gref->string-no-path TC} TL Q, Q) 
      (
        refine X G GL; 
        coq.say "illtyped solution:" {coq.term->string X}
      ) 
      (GL = [seal G]).
}}.
Elpi Typecheck.

Class EqSimpl (T : Type) := {eqb : T -> T -> bool}.

Global Instance EqU : EqSimpl unit := { eqb A B := true }.
Global Instance EqP {A B: Type} `(EqSimpl A, EqSimpl B) : EqSimpl (A * B) := { eqb A B := true }.

Elpi addClass EqSimpl.
Elpi compile EqU.
Elpi compile EqP.

Elpi Override TC solver All.

Check (_ : EqSimpl unit).
Check (_ : EqSimpl (unit * unit)).


