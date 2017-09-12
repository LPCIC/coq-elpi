From elpi Require Import elpi.

(* Coq-ELPI Tutorial

   If you are using CoqIDE please chose
   "coq-elpi" in

     Edit -> Preferences -> Colors

   in order to have nice syntax highlight
   of embedded code *)

(** Hello world *********************************** *)

(* An elpi program is defined by declaring its
   name an accumulating files or clauses in it *)

(* Set current program name to tutorial.hello *)
Elpi Program tutorial.hello.
(* Load coq-lib (contains the coq API) *)
Elpi Accumulate File "coq-lib.elpi".
(* Add a clause for main *)
Elpi Accumulate "
  main []     :- coq-say ""hello world"".
  main [Name] :- Msg is ""hello "" ^ Name, coq-say Msg.
".
(* Caveat: when clauses are accumulated from
   a .v file they are just strings, hence
   inner strings like "hello world" have to be
   escaped *)

(* Let's now invoke our first program *)
Elpi Run tutorial.hello " main []. ".
Elpi Run tutorial.hello " main [""Coq!""]. ".
Fail Elpi Run tutorial.hello " main [""too"",""many"",""args""]. ".

(* The "main" entry point is the default one.
   We can inoke a program by simply writing its name and
   arguments *)

Elpi tutorial.hello "Coq!".

(* One can define many programs. Since most programs
   accumulate the coq-lib file, and then accumulate some
   code, the following shortcut is provided. *)
Elpi Command tutorial.hello2 " main [] :- coq-say ""hello there"". ".
Elpi tutorial.hello2.

(* Programs (hence commands) are open ended: they can be extended *)
Elpi Program tutorial.hello "
  main [X,Y,Z] :- Msg is X ^ Y ^ Z, coq-say Msg. 
".
Elpi tutorial.hello "too" "many" "args".

(* Clauses are appended to the program, unless an anchor point
   is declared by naming a clause with :name "the name" *)

Elpi Command tutorial.hello3 "
:name ""error-empty-args""
  main []  :- fatal-error ""1 argument expected"".
  main [X] :- coq-say X. ".
Fail Elpi tutorial.hello3.

(* Let's graft this clause before the one giving an error *)
Elpi Accumulate "
:before ""error-empty-args""
  main [] :- coq-say ""fake argument"".
".
Elpi tutorial.hello3.
(* Note that when the name of Program or Command is not specified,
   Accumulate appends to the last Command/Program that was accumulated
   onto *)

(* The current set of clauses composing a program can
   be printed as follows *)
Elpi Print
  tutorial.hello3 (* program name *)
  "hello3.html"   (* output file  *)
  "pervasives.elpi" "coq-lib.elpi" "lp-lib.elpi" (* files to skip *).

(** Coq's terms **************** *)

Elpi Program tutorial.coq_HOAS.

(*

  Coq terms are represented in HOAS style, i.e. the bound variables of
  λProlog are used to represent Coq's ones.

*)

Elpi Accumulate " % this is an excerpt of coq-lib
kind term type.

% constants: inductive types, inductive constructors, definitions
type indt  @gref -> term. % nat, list, ...
type indc  @gref -> term. % O, S, nil, cons, ...
type const @gref -> term. % Nat.add, List.append, ...

% binders: to form functions, arities and local definitions
type lam  @name -> term -> (term -> term) -> term.         % fun x : t =>
type prod @name -> term -> (term -> term) -> term.         % forall x : t,
type let  @name -> term -> term -> (term -> term) -> term. % let x := v : T in

% other term formers: function application, pattern matching and recursion
type app   list term -> term.                   % app [hd|args]
type match term -> term -> list term -> term.   % match t p [branch])
type fix   @name -> int -> term -> (term -> term) -> term. % fix name rno ty bo

% Universes (for the ""sort"" term former)
kind universe type.
type prop universe.          % impredicative sort of propositions
type typ  @univ -> universe. % predicative sort of datatypes (carries a level)

type sort  universe -> term. % Prop, Type@{i}
".

(*  @name, @gref and @univ are Coq datatypes that are not directly
    accessible from an elpi program. 

    @name is a name hint, use for pretty printing only. 
       Two @name are always considered as equal.
    @gref are global names.
    @univ are universe level variables.

*)


(** Reading Coq's environment **************** *)

(* APIs to access Coq's environment are listed in
   coq-lib and the are all called coq-env-... 
   coq-locate maps a string to the corresponding
   term global constant/inductive/constructor.

*)

Elpi Command tutorial.env.read "
  print-ind GR :-
    coq-env-indt GR IsInd Lno LUno Ty Knames Ktypes,
    coq-say GR, coq-say Knames, coq-say Ktypes.
  print-const GR :-
    coq-env-const GR BO TY, coq-say TY, coq-say BO.
  main [X] :-
    coq-locate X (indt GR), print-ind GR,
    X_ind is X ^ ""_rect"", coq-locate X_ind (const GRI),
      print-const GRI.
".

Elpi tutorial.env.read "nat".

(** @name, @gref and @univ **************** *)

(* Recall that @name subterms are just for pretty printing *)

Definition c1 := fun x => x + 1.
Definition c2 := fun y => y + 2.

Elpi Command tutorial.env.read2 "
  main [] :-
    coq-locate ""c1"" (const GR1),
      coq-env-const GR1 (lam N1 _ _) _,
    coq-locate ""c2"" (const GR2),
      coq-env-const GR2 (lam N2 _ _) _,
    coq-say N1, coq-say N2,
    N1 = N2,          % gotcha: no ""logical"" meaning
    not(GR1 = GR2).   % @gref are global names
".

Elpi tutorial.env.read2.

(* This way the = predicate is alpha equivalence *)

Definition T1 := Type.
Definition T2 := Type. (* two unrelated universes *)

Elpi Command tutorial.env.read3 "
  main [] :-
    coq-locate ""T1"" (const GR1),
      coq-env-const GR1 (sort (typ T1)) _,
    coq-locate ""T2"" (const GR2),
      coq-env-const GR2 (sort (typ T2)) _,
    not (T1 = T2),     % not the same universe
    coq-say T1, coq-say T2,
    coq-univ-eq T1 T2. % we can constrain them to be equal
".

Elpi tutorial.env.read3.

(** Writing Coq's environment **************** *)

Elpi Command tutorial.env.write "
  int-2-nat 0 Z :- coq-locate ""O"" Z.
  int-2-nat N (app[S,X]) :-
    coq-locate ""S"" S,
    M is N - 1, int-2-nat M X.
  main [X,Name] :-
    coq-locate X (indt GR),
    coq-env-indt GR _ _ _ _ Kn _,
    length Kn N,
    int-2-nat N Nnat,
    coq-env-add-const Name Nnat hole _.
".

Elpi tutorial.env.write "nat" "nK_nat".
Print nK_nat. (* number of constructor of "nat" *)

(* hole is the equivalent of _ in Coq, a missing
   piece of information. *)

(** Quotation for Coq's terms **************** *)

Elpi Command tutorial.quotations "
  int-2-nat 0 {{0}}.
  int-2-nat N {{1 + lp:X}} :- M is N - 1, int-2-nat M X.
  main [X,Name] :-
    coq-locate X (indt GR),
    coq-env-indt GR _ _ _ _ Kn _,
    length Kn N,
    int-2-nat N Nnat,
    coq-env-add-const Name Nnat {{nat}} _.
".

(* Quotations work on untyped terms, i.e. _ are not filled in *)

Elpi tutorial.quotations "nat" "nK_nat2".
Print nK_nat2.

(* Double curly braces contain Coq's syntax that
   is elaborated to Elpi's one. lp:ident or lp:"some text"
   is the anti-quatation. *)

(** Queries other than main  ********************* *)

(* Even if main is the privileged entrypoint, any
   query can be run (this is usefule while building
   a larger program) *)

Elpi Run "
  coq-locate ""nat"" (indt GR),
  coq-env-indt GR _ _ _ _ Knames Ktypes,
  map Ktypes pp Kpretty.
".

(* In such case, the assignment of variables
   is printed once the query is over (debug output window).

   Elpi Run can also take in input the name of
   the program to load before the query is run
   (in case the current one does not fit)
 *)
Elpi Run tutorial.hello " main []. ".

(* Important: elpi comes with a type checker
   that is run against the program and the
   query only when Elpi Run is used.
   Elpi program.name does not invoke the type checker.

   Type errors are just Coq warnings, eg:
*)

Elpi Run " coq-say (app (sort prop)). ".

(** Tactics  ****************************** *)

(* Elpi Programs can be tactics. In that case the
   entry point is solve and an implementation of
   coq-declare-evar has to be provided (see coq-lib) *)

Elpi Program tutorial.tactic1.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  coq-declare-evar Evar Type Kont :- coq-evar Evar Type, Kont.

  solve [(goal Evar Type Attribues) as G] :-
    coq-say ""Goal:"", coq-say G,
    coq-say ""evar_map:"", coq-evd-print, % BUG: printed to stderr
    Evar = {{I}}.

".

(* Tactics can be invoked as regular programs, but this
   time Elpi becomes elpi *)

Goal True.
Proof.
elpi tutorial.tactic1.
Qed.

(* The evar map is represented as a set of constraints coq-evar.
   The goal is just one of them, and can be solved by assigning its
   corresponding evar. The coq-refiner file provides an elaborator
   written in elpi.  The following shortcult defines a program
   loading both coq-lib and coq-refiner *)

Elpi Tactic tutorial.tactic2 "
  solve [goal Evar Type Attribues] :- Evar = {{3}}.
  solve [goal Evar Type Attribues] :- Evar = {{I}}.
".

Goal True * nat.
Proof.
split.
- elpi tutorial.tactic2.

(* coq-refiner implements a elaborator (a type checker for terms
   containing holes and evars):
     of Term Type ElabTerm
   The of predicate recusively traverses Term.
   If it encounters an evar it generates a (typing) constraint
   on that evar. As soon as a term t is assigned to the evar
   the type checking is resumed, and the term t is cheked to be
   of the expected type.

   coq-refiner defines coq-declare-evar is such a way
   that a type checking constraint is declared for
   each evar.  In this clause Evar is assigned the value 3, its
   corresponding typing constraint is resumed and fails,
   since 3 : nat and not True. As a consequence the first clause
   fails, and the second one is tried. *)

- 
  elpi run " coq-evd-print ". (* BUG: prints to stderr *)
  elpi tutorial.tactic2.
Qed.

(* coq-refiner also implements a unification engine
     unify-eq T1 T2, unify-leq T1 T2 *)

Elpi Tactic tutorial.tactic3 "
  solve [goal Evar {{nat}} Attribues] :- Evar = {{3}}.
  solve [goal Evar {{bool}} Attribues] :- Evar = {{true}}.
  solve [goal Evar Any Attribues] :-
    unify-eq Any {{bool}}, Evar = {{false}}.
".

Definition Bool := bool.
Definition Nat := nat.

Lemma fast_path : bool * nat * Bool * Nat.
Proof.
split;[ split; [ split | ] | ].
- elpi tutorial.tactic3. (* uses the fast path *)
- elpi tutorial.tactic3.
- elpi tutorial.tactic3. (* needs full unification *)
  Show Proof. (* and indeed the solution was "false" *)
- Fail elpi tutorial.tactic3. (* no solve clause matches *)
Abort.

(* Note that in the third case the type checking constraint
   on Evar succeeds, i.e. of internally uses unify *)

(** More on @univ **************** *)

(* Working with universes is tricky, since the kernel
   only accepts a term if the required universe constraints
   are declared *)

Elpi Command tutorial.env.univ "
  main [] :-
    {{T1}} = (const GR1), coq-env-const GR1 SA TA, SA = sort (typ A), TA = sort (typ A+),
    {{T2}} = (const GR2), coq-env-const GR2 SB TB, SB = sort (typ B), TB = sort (typ B+),
    {{@eq}} = (indt GRE), coq-env-indt GRE _ _ _ (prod _ (sort (typ T)) _) _ _,    
    coq-univ-eq A B,
    coq-univ-sup A+ A++,
    coq-univ-leq A++ T,
    coq-env-add-const ""eq12"" (app[{{@refl_equal}}, TA, SA]) (app [{{@eq}},TA,SA,SB]) _.
".

Elpi tutorial.env.univ.

(* A much simpler approach is to invoke the type inference engine *)

Elpi Command tutorial.env.univ2 "
  main [] :-
    coq-elaborate {{refl_equal T1 : T1 = T2}} P PT,
    coq-env-add-const ""eq123"" P PT _.
".

Elpi tutorial.env.univ2.


(** Debugging  ********************* *)

(* 1. The @log macro (defined in lp-lib) takes a pattern for
   the goal to be printed.  It eats one line, and leaving it
   there commented does not hurt. *)
Elpi Program tutorial.debug.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  @log (int-2-nat _ _).
  int-2-nat 0 {{0}}.
  int-2-nat N {{1 + lp:X}} :- M is N - 1, int-2-nat M X.
".
Elpi Run " int-2-nat 3 X ".

(* caveat: hypothetical clauses come before the logger, so
   goal solved by them are not printed in the log *)


(* 2. The spy predicate prints a query before/after it is
      run. *)
Elpi Program tutorial.debug2.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  int-2-nat 0 {{0}}.
  int-2-nat N {{1 + lp:X}} :- M is N - 1, spy(int-2-nat M X).
".

Elpi Run " int-2-nat 3 X ".

(* caveat: if backtracking takes place, enter/exit prints
   are not well balanced *)


(* 3. The tracing facility of the interpreter. *)
Elpi Program tutorial.debug3.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  int-2-nat 0 {{0}}.
  int-2-nat N {{1 + lp:X}} :- M is N - 1, int-2-nat M X.
".
Elpi Trace.  (* Prints to the terminal *)
Elpi Run " int-2-nat 3 X ".

(* caveat: traces are long. one can limit it by using the
   numbers near the trace point and -trace-at. See 
   elpi -help form more details about tracing options. *)

Elpi Trace "-trace-on -trace-at run 9 14 -trace-only (run|assign)".
Elpi Run " int-2-nat 3 X ".
