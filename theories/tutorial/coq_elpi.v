From elpi Require Import elpi.

(* Coq-ELPI Tutorial

   If you are using CoqIDE please chose
   "coq-elpi" in

     Edit -> Preferences -> Colors

   in order to have nice syntax highlight
   of embedded code *)

(** Hello world *********************************** *)

(* There are two kinds of elpi programs: Commands
   and tactics.  An elpi program is defined by
   declaring its name (and kind: Command or Tactic)
   and then accumulating files or clauses in it. *)

(* Set current command name to tutorial.hello *)
Elpi Command tutorial.hello.
(* Add a clause for main *)
Elpi Accumulate "
  main []     :- coq-say ""hello world"".
  main [str Name] :- Msg is ""hello "" ^ Name, coq-say Msg.
".
(* Caveat: when clauses are accumulated from
   a .v file they are just strings, hence
   inner strings like "hello world" have to be
   escaped *)

(* Let's now invoke our first program *)
Elpi Query tutorial.hello " main []. ".
Elpi Query tutorial.hello " main [str ""Coq!""]. ".
Fail Elpi Query tutorial.hello " main [str ""too"",str ""many"",str ""args""]. ".

(* The "main" entry point is the default one.
   We can inoke a program by simply writing its name and
   arguments *)

Elpi tutorial.hello "Coq!".

(* It is so common to set the current command name and
   immediately accumulate some code that the following
   shortcut is provided. *)
Elpi Command tutorial.hello2 " main [] :- coq-say ""hello there"". ".
Elpi tutorial.hello2.

(* Elpi programs (commands or tactics) are open ended: they can
   be extended later on by accumulating extra code. *)
Elpi Command tutorial.hello "
  main [str X, str Y, str Z] :- Msg is X ^ Y ^ Z, coq-say Msg. 
".
Elpi tutorial.hello "too" "many" "args".

(* Clauses are appended to the program, unless an anchor point
   is declared by naming a clause with :name "the name" *)

Elpi Command tutorial.hello3 "
:name ""error-empty-args""
  main []  :- fatal-error ""1 argument expected"".
  main [str X] :- coq-say X. ".
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

(* Even if main is the privileged entrypoint, any
   query can be run (this is useful while building
   a larger program) *)

Elpi Query "
  coq-say ""This is not main"", X is 2 + 3.
".

(* In such case, the assignment of variables
   is printed once the query is over (debug output window).

   Elpi Query can also take in input the name of
   the program to load before the query is run
   (in case the current one does not fit)
 *)
Elpi Query tutorial.hello " main []. ".

(* Important: elpi comes with a type checker. *)
Elpi Command tutorial.illtyped "
  main _ :- coq-say (app (sort prop)).
".
Fail Elpi Typecheck tutorial.illtyped.

(* Note that the type checker is also invoked any time
   a query is run by hand, while it is not run when a program
   is executed directly (type checking is expensive). *)

Fail Elpi Query tutorial.illtyped " main []. ".
Elpi tutorial.illtyped. (* No typing here *)

(* Types play no role at run time, so executing ill typed
   programs is not a big deal.  Still you may want to fix
   type errors, or use unsafe-cast to silence the type checker:
   most of the times type errors are real errors *) 

(** Gallina **************** *)

Elpi Command tutorial.coq_HOAS.

(*

  Coq terms are represented in HOAS style, i.e. the bound variables of
  λProlog are used to represent Coq's ones.
  
  An excerpt of coq-lib follows:

*)

(*

% term is a data type name. its constructors follow
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

% sorts
kind universe type.          % another data type name
type sort universe -> term. % Prop, Type@{i}

type prop universe.          % impredicative sort of propositions
type typ  @univ -> universe. % predicative sort of datatypes (carries a level)

*)

(*

  Note how binders (lam, let, prod and fix) carry a (λProlog) function.

  In this syntax, the body of "plus" (the addition over natural numbers)
  looks like that:

   fix `add` 0 (prod `n` (indt "nat") x0 \ prod `m` (indt "nat") x1 \ indt "nat")
     x0 \
       lam `n` (indt "nat") x1 \
       lam `m` (indt "nat") x2 \
         match x1 (lam `n` (indt "nat") x3 \ indt "nat")
         [x2,
         (lam `p` (indt "nat") x3 \
            app [indc "S", app [x0, x3, x2]])]

  Where 0 is the position of the decreasing argument.  We will learn later on
  how to fetch such data from the environment of Coq.

*)

(*

  The @name, @gref and @univ datatypes are Coq datatypes.
  Terms of these types can only be built going trough the API provided
  by the coq-elpi plugin.

  A term of type @name is just a name hint, it is used for pretty printing
  only. Indeed any two @name are considered as equal. A name hint "x" can
  be created via the (coq-string->name "x") API, or with the dedicated syntax
  `x` (backticks, not apostrophes).

*)

Elpi Query "
  `x` = `y`,
  coq-string->name ""n"" N.
".

(* 

  A term of type @gref is the name of a global object (an inductive type or constructor,
  a definition or a theorem).  The coq-locate API can be used to generate terms in the @gref
  type.  There is no shortcut syntax to write a @gref, even if the glob quotation we see
  later can sometime help in doing that.

*)

Elpi Query "
  coq-locate ""S"" (indc GRS),
  coq-locate ""O"" (indc GRO),
  not(GRS = GRO).
".

(*

  Finally a @univ is a universe level variable. Elpi holds a store of constraints
  on the terms of type @univ and provides API to relate such terms. The names of
  such APIs begin with coq-univ.
  Note: the user seldom declare universe constraints by hand, he rather invokes
  the elaborator to infer them as we will see later.

*)

Elpi Query "
  coq-univ-new [] U, coq-univ-new [] V,
  coq-univ-sup U U+1,
  coq-univ-leq U V,
  not(coq-univ-leq U+1 U). % This constraint can't be allowed in the store!
".

(** Reading Coq's environment **************** *)

(* 

   APIs to access Coq's environment are listed in
   coq-lib and the are all called coq-env-... 
   
   As we have seen already, coq-locate maps a string to the corresponding
   term global constant/inductive/constructor.

*)

Elpi Command tutorial.env.read "
  print-ind GR :-
    coq-env-indt GR IsInd Lno LUno Ty Knames Ktypes,
    coq-say GR, coq-say Knames, coq-say Ktypes.
  print-const GR :-
    coq-env-const GR BO TY, coq-say TY, coq-say BO.
  main [str X] :-
    coq-locate X (indt GR), print-ind GR,
    X_ind is X ^ ""_rect"", coq-locate X_ind (const GRI),
      print-const GRI.
".

Elpi tutorial.env.read "nat".

(** Writing Coq's environment **************** *)

(* 

   APIs to access Coq's environment are listed in
   coq-lib and the are all called coq-env-add... 

   In this API the hole term constructor is used
   to represent a missing piece of info, for example
   hole can be provided as the body of an Axiom, or
   as the type of a constant (that will be inferred).

   The following code uses this API to provide a command
   that given the name of a Coq inductive type generates
   a constant of type nat whose value is the number of
   constructors of the given inductive type.

*)

Elpi Command tutorial.env.write "
  int->nat 0 Z :- coq-locate ""O"" Z.
  int->nat N (app[S,X]) :-
    coq-locate ""S"" S,
    M is N - 1, int->nat M X.
  main [str IndName, str Name] :-
    coq-locate IndName (indt GR),
    coq-env-indt GR _ _ _ _ Kn _,       % get the names of the constructors
    length Kn N,                        % count them
    int->nat N Nnat,                    % turn the integer into a nat 
    coq-env-add-const Name Nnat hole _ (const NewGRForName). % save it
".

Elpi tutorial.env.write "nat" "nK_nat".
Print nK_nat. (* number of constructor of "nat" *)

(** Quotation for Coq's terms **************** *)

(*

   Writing Coq terms by hand is tedious.  The so called "glob quotation"
   comes to the rescue.  The Coq syntax for terms can be placed
   between double curly braces.  Coq-elpi translates it to the HOAS
   representation of terms just before the execution of the program.

   The syntax for anti-quotation is lp:ident or lp:"more complex term"

   Let's rewrite the previous program using the qutation.

*)

Elpi Command tutorial.quotations "
  int->nat 0 {{0}}.
  int->nat N {{S lp:X}} :- M is N - 1, int->nat M X.
  main [str X, str Name] :-
    coq-locate X (indt GR),
    coq-env-indt GR _ _ _ _ Kn _,
    length Kn N,
    int->nat N Nnat,
    coq-env-add-const Name Nnat {{nat}} _ _.
".

Elpi tutorial.quotations "nat" "nK_nat2".
Print nK_nat2.

(* Quotations work on untyped terms (called glob terms in the sources of Coq).
   What is relevant is that implict arguments (_ in the syntax of Coq) are
   not filled in. This is the role of the elaborator, not of the
   quotation itself.

   Implicit arguments are represented by the hole term constructor.
*)

Elpi Query "
  T = {{0 = 1}}, % Note, the iplicit argument of eq is not resolved
  coq-elaborate T T1 Ty. % Invoke standard Coq elaborator
".

(** Tactics  ****************************** *)

(* Elpi Programs can be tactics. In that case the
   entry point is solve (and not main). *)

Elpi Tactic tutorial.tactic1.
Elpi Accumulate "

  solve Arguments [goal Ctx Evar Type Attribues] [] :-
    coq-say ""Goal:"" Ctx ""|-"" Evar "":"" Type, % Note: coq-say is variadic
    coq-say ""Proof state:"", coq-evd-print,
    coq-say ""Arguments: "" Arguments,
    Ctx => of {{fun _ => I}} Type Evar. % We invoke elpi's elaborator

".

(* Tactics can be invoked as regular programs, but this
   time Elpi becomes elpi. Arguments can either be
   strings (no double quote needed if the string happens to be
   an possible qualified name) or terms (always between parentheses) *)

Lemma tutorial1 x y : x + 1 = y -> True.
Proof. 
elpi tutorial.tactic1 "argument1" argument2 (x).
Qed.

(* The proof state (evar_map in Coq's slang) is represented as a set
   of constraints about the evar predicate.

   The goal is just one of them, and can be solved by assigning its
   corresponding evar. The coq-refiner file provides an elaborator
   written in elpi.  When an elpi program is declared as a Tactic,
   coq-refiner is automatically accumulated. *)

Elpi Tactic tutorial.tactic2 "
  solve _ [goal Ctx Evar Type Attribues] _ :- Evar = {{3}}.
  solve _ [goal Ctx Evar Type Attribues] _ :- Evar = {{I}}.
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

   coq-refiner wires things up in such a way
   that a type checking constraint is declared for
   each evar.  In the first clause Evar is assigned the value 3, its
   corresponding typing constraint is resumed and fails,
   since 3 : nat and not True. As a consequence the first clause
   fails, and the second one is tried. *)

- 
  elpi query " coq-evd-print ".
  elpi tutorial.tactic2.
Qed.

(* coq-refiner also implements a unification engine
     unify-eq T1 T2, unify-leq T1 T2 *)

Elpi Tactic tutorial.tactic3 "
  solve _ [goal Ctx Evar {{nat}} Attribues] _ :- Evar = {{3}}.
  solve _ [goal Ctx Evar {{bool}} Attribues] _ :- Evar = {{true}}.
  solve _ [goal Ctx Evar Any Attribues] _ :-
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


(** Ltac's match goal with  ************************* *)

(*

    Ltac provides a special syntactic construct to inspect
    a goal called "match goal with ... end".

    It is easy to implement it, since it is made of two components:
    - a first order matching procedure (no unfolding)
    - non-determinism to "pair" hypothesis and patterns for the context.

    The first ingredient is the standard copy predicate
    The second ingredient is the composition of the forall and exists
      standard list "iterators".

*)

Elpi Tactic tutorial.ltac "

kind goal-pattern type.
type with @goal-ctx -> term -> prop -> goal-pattern.
pred pattern-match i:goal, o:goal-pattern.
pred pmatch i:term, o:term.
pred pmatch-hyp i:prop, o:prop.

:name ""pmatch:syntactic""
pmatch T P :- copy T P.

% If one asks for a decl, we also find a def
pmatch-hyp (decl X N Ty)    (decl X N PTy) :- pmatch Ty PTy.
pmatch-hyp (def X N Ty _ _) (decl X N PTy) :- pmatch Ty PTy.
pmatch-hyp (def X N Ty B _) (def X N PTy PB _) :- pmatch B PB, pmatch Ty PTy.

% We first match the goal, then we see if for each hypothesis pattern
% there exists a context entry that matches it, finally we test the condition.
pattern-match (goal Hyps _ Type _) (with PHyps PGoal Cond) :-
  pmatch Type PGoal,
  (forall PHyps p\ exists Hyps h\ pmatch-hyp h p), % forall and exists are in lp-lib
  Cond.

solve _ [(goal _ E _ _) as G] _ :-
  pattern-match G (with [decl X NameX T,decl Y NameY T] T (not(X = Y))),
  coq-say ""Both"" NameX ""and"" NameY ""solve the goal, picking the first one"",
  E = X.

".

Lemma ltac1 (x y : bool) (H : x = y) (H0 : y = y) (H1 := H) (H2 : x = x) : x = y.
Proof. 
elpi tutorial.ltac.
Qed.

(* Let's now extract higher order terms from the context, like the
   predicate about "y" *)

Elpi Accumulate "

pred pierce i:term, o:term.
pierce T PT :- (copy hole _ :- !) => copy T PT.

pred context-of i:term, i:term, o:(term -> term).
context-of What Where F :- pi x\ (copy What x) => copy Where (F x).

constant? F :- pi x y\ F x = F y.

solve _ [(goal Ctx E ETy _) as G] _ :-
  pattern-match G (with [decl X NameX Ty] T (context-of T Ty C, not(constant? C))),
  Ctx => of {{let ctx := fun y => lp:C y in _}} ETy E.
".

Lemma ltac2 x (H : exists y, x <> 0 /\ y = x) : x <> 0 .
Proof.
elpi tutorial.ltac.
change (ctx (x<>0)) in H.
Abort.

(** Debugging  ********************* *)

(* 1. The @log macro (defined in lp-lib) takes a pattern for
   the goal to be printed.  It eats one line, and leaving it
   there commented does not hurt. *)
Elpi Command tutorial.debug.
Elpi Accumulate "
  @log (int->nat I N).
  int->nat 0 {{0}}.
  int->nat N {{1 + lp:X}} :- M is N - 1, int->nat M X.
".
Elpi Query " int->nat 3 X ".

(* caveat: hypothetical clauses come before the logger, so
   goal solved by them are not printed in the log *)


(* 2. The spy predicate prints a query before/after it is
      run. *)
Elpi Command tutorial.debug2.
Elpi Accumulate "
  int->nat 0 {{0}}.
  int->nat N {{1 + lp:X}} :- M is N - 1, spy(int->nat M X).
".

Elpi Query " int->nat 3 X ".

(* caveat: if backtracking takes place, enter/exit prints
   are not well balanced *)


(* 3. The tracing facility of the interpreter. *)
Elpi Command tutorial.debug3.
Elpi Accumulate "
  int->nat 0 {{0}}.
  int->nat N {{1 + lp:X}} :- M is N - 1, int->nat M X.
".
Elpi Trace.  (* Prints to the terminal *)
Elpi Query " int->nat 3 X ".

(* caveat: traces are long. one can limit it by using the
   numbers near the trace point and -trace-at. See 
   elpi -help form more details about tracing options. *)

Elpi Trace "-trace-on -trace-at run 9 14 -trace-only (run|assign)".
Elpi Query " int->nat 3 X ".
