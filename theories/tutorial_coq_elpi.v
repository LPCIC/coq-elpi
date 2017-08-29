Require Import elpi.

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
Elpi tutorial.hello.
Elpi tutorial.hello "user!".
Fail Elpi tutorial.hello "too" "many" "arguments".

(* One can define many programs *)
Elpi Program tutorial.hello2.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate " main [] :- coq-say ""hello there"". ".
Elpi tutorial.hello2.

(* And extend old programs *)
Elpi Program tutorial.hello.
Elpi Accumulate " main [X,Y,Z] :- Msg is X ^ Y ^ Z, coq-say Msg. ".
Elpi tutorial.hello "too" "many" "arguments".

(* Clauses are appended to the program, unless an anchor point
   is declared by naming a clause with :name "the name" *)

Elpi Program tutorial.hello3.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
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

    @name is a name hint, use for pretty printing only. Two @name are always
       considered as equal.
    @gref are global names.
    @univ are universe level variables.

*)


(** Reading Coq's environment **************** *)

(* APIs to access Coq's environment are listed in
   coq-lib and the are all called coq-env-... 
   coq-locate maps a string to the corresponding
   term global constant/inductive/constructor.

*)

Elpi Program tutorial.env.read.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
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

Elpi Program tutorial.env.read2.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  main [] :-
    coq-locate ""c1"" (const GR1),
      coq-env-const GR1 (lam N1 _ _) _,
    coq-locate ""c2"" (const GR2),
      coq-env-const GR2 (lam N2 _ _) _,
    coq-say N1, coq-say N2,
    N1 = N2,          % gotcha: no ""logical"" meaning
    not(GR1 = GR2).   % @gref are global names
".

Elpi Run tutorial.env.read2 " main [] ".

(* This way the = predicate is alpha equivalence *)

Definition T1 := Type.
Definition T2 := Type. (* two unrelated universes *)

Elpi Program tutorial.env.read3.
Elpi Accumulate File "coq-lib.elpi".

Elpi Accumulate "
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

Elpi Program tutorial.env.write.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
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

Elpi Program tutorial.quotations.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
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

(** More on @univ **************** *)

(* Working with universes is tricky, since the kernel
   only accepts a term if the required universe constraints
   are declared *)

Elpi Program tutorial.env.univ.
Elpi Accumulate File "coq-lib.elpi".

Elpi Accumulate "
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

Elpi Program tutorial.env.univ2.
Elpi Accumulate File "coq-lib.elpi".

Elpi Accumulate "
  main [] :-
    coq-elaborate {{refl_equal T1 : T1 = T2}} P PT,
    coq-env-add-const ""eq123"" P PT _.
".

Elpi tutorial.env.univ2.


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
