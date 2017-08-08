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

(* Set current program name to tutorial.first *)
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

Elpi Accumulate "
:before ""error-empty-args""
  main [] :- coq-say ""fake argument"".
".
Elpi tutorial.hello3.

Elpi Print tutorial.hello3 "hello3.html" 
  "pervasives.elpi" "coq-lib.elpi" "lp-lib.elpi".


(** Coq's terms **************** *)

(* see the header of coq-lib *)

(** Reading Coq's environment **************** *)

(* APIs to access Coq's environment are listed in
   coq-lib and the are all called coq-env-* *)

Elpi Program tutorial.env.read.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  print-ind GR :-
    coq-env-indt GR IsInd Lno LUno Ty Knames Ktypes,
    coq-say GR, coq-say Knames, coq-say Ktypes.
  main [X] :- coq-locate X (indt GR), print-ind GR.
".

Elpi tutorial.env.read "nat".

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
Print nK_nat.

(* hole is the equivalent of _ in Coq, a missing
   piece of information, while (app [hd,args1,...,argn]) *)

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

(* Important: elpi comes with a type checker
   that is run against the program and the
   query only when Elpi Run is used.
   Elpi progra.name does not invoke the type checker.
*)

(* In such case, the assignment of variables
   is printed once the query is over.

   Elpi Run can also take in input the name of
   the program to load before the query is run
   (in case the current one does not fit)
 *)
Elpi Run tutorial.hello " main []. ".

(** Debugging  ********************* *)

(* 1. The @log macro takes a pattern for
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
