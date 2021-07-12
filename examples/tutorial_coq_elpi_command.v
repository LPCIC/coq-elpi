From elpi Require Import elpi.
(**
   Elpi is an extension language that comes as a library
   to be embedded into host applications such as Coq.

   Elpi is a variant of λProlog enriched with constraints.
   λProlog is a programming language designed to make it easy
   to manipulate abstract syntax trees containing binders.
   Elpi extends λProlog with programming constructs that are
   designed to make it easy to manipulate abstract syntax trees
   containing metavariables (also called unification variables, or
   evars in the Coq jargon).

   This software, "coq-elpi", is a Coq plugin embedding Elpi and
   exposing to the extension language Coq spefic data types (e.g. terms)
   and API (e.g. to declare a new inductive type).

   In order to get proper syntax highlighting using VSCode please install the
   "gares.coq-elpi-lang" extension. In CoqIDE please chose "coq-elpi" in
   Edit -> Preferences -> Colors.
*)

(** ----------------------- ----------------------- -----------------------

   This tutorial focuses on the implementation of Coq commands.

   This tutorial assumes the reader is familiar with Elpi and the HOAS
   representation of Coq terms; if it is not the case, please take a look at
   these other tutorials first:
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_elpi_lang.v
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_coq_elpi_HOAS.v

   - Defining commands
   - Example: Synthesizing a term

*)


(** ------------------------- Defining commands ---------------------------- *)


(**
   In the previous tutorial we have seen that an Elpi program can be declared
   using the "Elpi Program <name> lp:{{ code }}" command. The resulting program
   is obtained by accumulating the code for:

   - built-in predicates (eg "coq.say") and first order terms
     https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

   - higher order terms (eg Coq terms, detailed later in this tutorial)
     https://github.com/LPCIC/coq-elpi/blob/master/elpi/coq-HOAS.elpi

   - the user provided "<code>"

   Later one can accumulate on top of this other clauses
   via "Elpi Accumulate".

   The more specific commands "Elpi Command" and "Elpi Tactic" take "<code>"
   from predefined templates, respectively:

   - https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template.elpi
   - https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi

   The "Elpi Accumulate ..." family of commands lets one accumulate clauses
   taken from:

   - verbatim text "Elpi Accumulate lp:{{ <code> }}"
   - source files "Elpi Accumulate File <path>"
   - data bases (Db) "Elpi Accumulate Db <name>"

   A "Db" can be create with the command:

   - "Elpi Db <name> lp:{{ <code> }}"

   and a Db can be later extended via "Elpi Accumulate".
   Indeed a Db is pretty much like a regular program but can be shared among
   other programs (a program accumulates a Db by name, not by contents).

   Let's define a Db.
  *)

  Elpi Db age.db lp:{{ % We like Db names to end in a .db suffix

  % A typical Db is made of one main predicate
  pred age o:string, o:int.

  % the Db is empty for now, we put a clause giving a descriptive error
  % and we name that clause "age.fail".
  :name "age.fail"
  age Name _ :- coq.error "I don't know who" Name "is!".

}}.

(**
   Elpi clauses can be given a name via the ":name" attribute. Named clauses
   serve as anchor-points when clauses are added to the Db.

   Let's define a Command that makes use of a Db.
*)

Elpi Command tutorial.
Elpi Accumulate Db age.db.
Elpi Accumulate lp:{{

  main []         :- coq.say "hello world".

  main [str Name] :- coq.say "hello" Name ", you are" {age Name}.

}}.
Elpi Typecheck. (* We will detail later what this is for *)

(** The entry point for commands is "main" that receives a list of
    arguments. See https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
    for their constructors/types. Here we use "str" that carries a string.

    Elpi provides a syntax to call (query) the standard entry point of commands
    (and later tactics).
*)

Elpi tutorial.           (** Elpi Query tutorial lp:{{ main [] }} *)
Fail Elpi tutorial bob.  (** Elpi Query tutorial lp:{{ main [str "bob"] }} *)

(**
   Let's put some data in the Db. Given that the Db contains a catch-all clause,
   we need the new one to be put before it. *)

Elpi Accumulate age.db lp:{{

  :before "age.fail"
  age "bob" 24.

}}.

Elpi tutorial bob.

(**
    Elpi programs, like Dbs, are open ended: they can
    be extended later on by accumulating extra code. The same consideration
    about named clauses as anchor point and the :before attribute apply.
*)
Elpi Accumulate tutorial lp:{{

  main _ :- coq.say "usage: tutorial [name]".

}}.
Elpi tutorial "too" "many" "args".


(**
  Arguments can either be numbers, strings (no double quote needed if the string
  happens to be a qualified name), terms (always between parentheses) or
  declarations (as Record, Inductive or Definition).
*)

Elpi Command show_arguments.
Elpi Accumulate lp:{{

  main Arguments :-
    coq.say "Arguments: " Arguments.

}}.
Elpi Typecheck.
Elpi show_arguments "argument1" argum.ent2 3 (1 = 2).

(**
  Terms are passed "raw", in the sense that no elaboration has been
  performed. In the example above the type argument to "eq" has not
  been synthesized to be "nat". As we see later, the "coq.typecheck" API
  can be used to satisfy typing constraints.
*)

(** Commands can be exported to the usual name space of command with
    Elpi Export *)

Elpi Export show_arguments.

show_arguments 1 "2" (3).

(**
   Elpi comes with a type checker. It is invoked any time
   a query is run by hand via "Elpi Query", or when invoked via
   "Elpi Typecheck".
   It is not run when a "Command" or "Tactic" in invoked via its main
   entry point.
*)
Elpi Command illtyped.
Elpi Accumulate lp:{{
  pred test o:bool.
  test (tt ^ "3").
}}.
Fail Elpi Typecheck illtyped.

(** -------------------- Example: Synthesizing a term ---------------------- *)

(**
   Synthesizing a term typically involves reading an existing declaration
   and writing a new one. The relevant APIs are in the "coq.env.*" namespace
   and are named after the global refence they manipulate, eg "coq.env.const"
   for reading and "coq.env.add-const" for writing.

   Here we implement a little command that given an inductive type
   generates a term of type nat whose value is the number of constructors
   of the given inductive type.
*)

Elpi Command constructors_num.

Elpi Accumulate lp:{{

  pred int->nat i:int, o:term.
  int->nat 0 {{0}}.
  int->nat N {{S lp:X}} :- M is N - 1, int->nat M X.

  main [str IndName, str Name] :-
    coq.locate IndName (indt GR),
    coq.env.indt GR _ _ _ _ Kn _,         % get the names of the constructors
    std.length Kn N,                      % count them
    int->nat N Nnat,                      % turn the integer into a nat
    coq.env.add-const Name Nnat _ _ _. % save it
}}.
Elpi Typecheck.

Elpi constructors_num "bool" "nK_bool".
Print nK_bool. (* number of constructor of "bool" *)
Elpi constructors_num "False" "nK_False".
Print nK_False.


