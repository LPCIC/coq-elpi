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
   - Arguments
   - Processing raw arguments
   - Example: Synthesizing a term
   - Example: Abstracting an inductive
   - Using DBs to store data across calls
   - Attributes and Export

*)


(** ------------------------- Defining commands ---------------------------- *)


(**

   Lets declare a simple program, called "hello"

*)
Elpi Command hello.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "Hello" Arguments.

}}.
Elpi Typecheck.

(*

   The program declaration is made of 3 parts.
   
   The first one "Elpi Command hello." sets the current program to hello.
   Since it is declared as a "Command" some code is loaded automatically:
   - built-in predicates (eg "coq.say") and data types (eg Coq terms)
     https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
   - some utilities, like "copy" or "whd1"
     https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template.elpi


   The second one "Elpi Accumulate ..." loads some extra code.
   The "Elpi Accumulate ..." family of commands lets one accumulate code
   taken from:
   - verbatim text "Elpi Accumulate lp:{{ <code> }}"
   - source files "Elpi Accumulate File <path>"
   - data bases (Db) "Elpi Accumulate Db <name>"
   Accumulating code via inline text of file is equivalent, the AST of code
   is stored in the .vo file (the external file does not need to be installed).
   We postpone the description of data bases to a dedicated section.

   Once all the code is accumulated "Elpi Typecheck" verifies that the
   code does not contain the most frequent kind of mistakes. This command
   considers some mistakes minor and only warns about them. You can
   pass "-w +elpi.typecheck" to coqc to turn these warnings into errors.

   We can now run our program!

*)

Elpi hello "world!".

(*

   You should see

     Hello [str world!]

   The  string "world!" we passed to the command is received by the code
   as (str "world!").

*)

(** ------------------------- Arguments ---------------------------- *)

Elpi hello 46.
Elpi hello there.

(*

  This time we passed to the command a number and an identifier, and we get

    Hello [int 46]
    Hello [str there]

  Identifiers are received as strings, and can contain dots, but no spaces
*)

Elpi hello my friend.
Elpi hello this.is.a.qualified.name.

(*

  Indeed the first invocation passes two arguments, of type string, while
  the second a single one, again a string containing dots.

    Hello [str my, str friend]
    Hello [str this.is.a.qualified.name]

  There are a few more types of arguments a command can receive:
  - terms, delimited by "(" and ")"
  - toplevel declarations, like "Inductive ..", "Definition ..", etc..
    which are introduced by their characterizing keyword.

  Lets try with a term

*)

Elpi hello (0 = 1).

(**

  We get

    Hello 
      [trm (app [global (indt «eq»),
                 X0,
                 global (indc «O»), 
                 app [global (indc «S»), global (indc «O»)]])]

  Terms are received "raw", in the sense that no elaboration has been
  performed. In the example above the type argument to "eq" has not
  been synthesized to be "nat". As we see later, the "coq.typecheck" API
  can be used to satisfy typing constraints.

*)

Elpi hello Definition test := 0 = 1.
Elpi hello Record test := { f1 : nat; f2 : f1 = 1 }.

(*

  Global declarations are received raw as well

    Hello [const-decl test 
      (some (app [global (indt «eq»), X0, global (indc «O»), 
                   app [global (indc «S»), global (indc «O»)]]))
      (arity X1)]
    
    Hello [indt-decl
      (record test (sort (typ X0)) Build_test 
    	  (field [coercion ff, canonical tt] f1 (global (indt «nat»)) c0 \
         field [coercion ff, canonical tt] f2 
           (app
             [global (indt «eq»), X1 c0, c0, 
              app [global (indc «S»), global (indc «O»)]]) c1 \
         end-record))]

  See the "argument" data type in 
    https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
  for a detailed decription of all the arguments a command can receive.

*)

(** -------------------- Processing raw arguments --------------------- *)

(*
    There are two ways to process term arguments.
    
*)

Elpi Command check_arg.
Elpi Accumulate lp:{{

  main [trm T] :-
    std.assert-ok! (coq.typecheck T Ty) "argument illtyped",
    coq.say "The type of" T "is" Ty.

}}.
Elpi Typecheck.

Elpi check_arg (1 = 0).
Fail Elpi check_arg (1 = true).

(*

  The command "check_arg" received a term T and type checks it, then it
  prints the term and its type.

  The "coq.typecheck" API has 3 arguments, a term, its type and a diagnostic
  which can either be "ok" or "(error Message)". The "std.assert-ok!" combinator
  checks if the diagnostic is ok, and if not it prints the error message and
  bails out.
  
  The first invocation succeeds
  
    The type of 
      app [global (indt «eq»), global (indt «nat»), 
           app [global (indc «S»), global (indc «O»)],
           global (indc «O»)]
    is 
      sort prop

  The second one fails

    argument illtyped: Illegal application: 
    The term "@eq" of type "forall A : Type, A -> A -> Prop"
    cannot be applied to the terms
     "nat" : "Type"
     "1" : "nat"
     "true" : "bool"
    The 3rd term has type "bool" which should be coercible to "nat".

*)

Coercion bool2nat (b : bool) := if b then 1 else 0.
Fail Elpi check_arg (1 = true).
Check (1 = true).

(*
  The command still fails even if we told Coq how to inject booleans values
  into the natural numbers. Indeed the Check commands works.

  The "coq.typecheck" API modifies the term in place, it can assign
  implicit arguments (like the type parameter of eq) but cannot modify the
  structure of th term. To do so, one has to use the "coq.elaborate-skeleton"
  API
*)

Elpi Command elaborate_arg.
Elpi Accumulate lp:{{

  main [trm T] :-
    std.assert-ok! (coq.elaborate-skeleton T Ty T1) "illtyped arg",
    coq.say "T=" T,
    coq.say "T1=" T1,
    coq.say "Ty=" Ty.
    
}}.
Elpi Typecheck.

Elpi elaborate_arg (1 = true).

(* 

   Remark how T is not touched by the API, and how T1 is a copy where
   the hole after eq was synthesized and the value true injected to nat
   by using bool2nat.
 
     T=  app [global (indt «eq»), X0,
              app [global (indc «S»), global (indc «O»)], 
              global (indc «true»)]
     T1= app [global (indt «eq»), global (indt «nat»), 
              app [global (indc «S»), global (indc «O»)], 
              app [global (const «bool2nat»), global (indc «true»)]]
     Ty= sort prop

   It is also possible to manipulate term arguments before typechecking
   them, but note that all the considerations on Holes in the tutorial about
   the HOAS representation of Coq terms apply here. 
*)

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
  int->nat 0 {{ 0 }}.
  int->nat N {{ S lp:X }} :- M is N - 1, int->nat M X.

  main [str IndName, str Name] :-
    coq.locate IndName (indt GR),
    coq.env.indt GR _ _ _ _ Kn _,         % get the names of the constructors
    std.length Kn N,                      % count them
    int->nat N Nnat,                      % turn the integer into a nat
    coq.env.add-const Name Nnat _ _ _.    % save it

}}.
Elpi Typecheck.

Elpi constructors_num bool nK_bool.
Print nK_bool. (* number of constructor of "bool" *)
Elpi constructors_num False nK_False.
Print nK_False.

(** -------------------- Example: Abstracting an inductive --------------- *)

Elpi Command abstract.

Elpi Accumulate lp:{{

  pred prime i:string, o:string.
  prime S S1 :- S1 is S ^ "'".

  main [str Ind, trm Param] :-
    
    std.assert-ok! (coq.elaborate-skeleton Param PTy P) "illtyped parameter",
    
    coq.locate Ind (indt I),
    coq.env.indt-decl I Decl,
    NewDecl = parameter "A" explicit PTy Decl',
    (pi a\ copy P a => copy-indt-decl Decl (Decl' a)),
    coq.rename-indt-decl (=) prime prime NewDecl DeclRenamed,
    std.assert-ok! (coq.typecheck-indt-decl DeclRenamed) "can't be abstracted",
    coq.env.add-indt DeclRenamed _.

}}.
Elpi Typecheck.

Inductive tree := leaf | node : tree -> option nat -> tree -> tree.

Elpi abstract tree (option nat).
Print tree'.

(*
Inductive tree' (A : Set) : Set :=
	leaf' : tree' A | node' : tree' A -> A -> tree' A -> tree' A
*)

(** ------------------ Using DBs to store data across calls ---------------- *)

(**

   A Db can be create with the command:

   - "Elpi Db <name> lp:{{ <code> }}"

   and a Db can be later extended via "Elpi Accumulate".

   Indeed a Db is pretty much like a regular program but can be shared among
   other programs (a program accumulates a Db by name) and can be extended by
   Elpi programs as well thanks to the API coq.elpi.accumulate.

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

Elpi Command age.
Elpi Accumulate Db age.db.  (* we accumulate the Db *)
Elpi Accumulate lp:{{

  main [str Name] :-
    age Name A,
    coq.say Name "is" A "years old".

}}.
Elpi Typecheck. 

Fail Elpi age bob.

(**
   Let's put some data in the Db. Given that the Db contains a catch-all clause,
   we need the new one to be put before it. *)

Elpi Accumulate age.db lp:{{

  :before "age.fail"
  age "bob" 24.

}}.

Elpi age bob.

(*

  Elpi programs can extend a Db as well

*)

Elpi Command set_age.
Elpi Accumulate Db age.db.
Elpi Accumulate lp:{{
  main [str Name, int Age] :-
    coq.elpi.accumulate _ "age.db" (clause _ (before "age.fail") (age Name Age)).
  
}}.
Elpi Typecheck.

Elpi set_age "alice" 21.
Elpi age "alice".


(** ----------------------- Attributes and Export -------------------------- *)

(*

   Elpi programs can be prefixed with attributes, like #[local].
   Attributes are not passed as arguments but rather as a clause.
   
*)

Elpi Command attr.
Elpi Accumulate lp:{{

  main _ :-
    attributes A,
    coq.say A.

}}.

#[this, more(stuff="33")] Elpi attr.

(*
[attribute elpi.loc (leaf-loc File "(stdin)", line 3, column 35, characters 33-37:), 
 attribute this (leaf-str ), 
 attribute more (node [attribute stuff (leaf-str 33)])]
*)

Elpi Command parse_attr.
Elpi Accumulate lp:{{

  pred some-code.
  some-code :- get-option "more.stuff" N, get-option "this" B, coq.say N B.

  main _ :-
    attributes A,
    coq.parse-attributes A [
      att "this" bool,
      att "more.stuff" int,
    ] Opts,
    coq.say Opts,
    Opts => some-code.

}}.

#[this, more(stuff="33")] Elpi parse_attr.
Fail #[unknown] Elpi parse_attr.
(*
33 tt
The command has indeed failed with message:
Attribute unknown is not supported
*)

(*

  Elpi programs can be exported as regular Coq commands, so that the
  final user does not need to type Elpi to invoke them.

*)

Elpi Command say.
Elpi Accumulate lp:{{ main [str S] :- coq.say S. }}.
Elpi Typecheck.
Elpi Export say.

say "That is all folks!".

(*

  Not quite. Coq offers no equivalent of Tactic Notation for commands.
  Still Elpi commands accept any symbol or keyword as strings.

*)

Elpi Command go.
Elpi Accumulate lp:{{
  main [str Src, str "=>", str Tgt, str "/", str F] :- !,
    coq.say "going from" Src "to" Tgt "via" F.
  main _ :- coq.error "Parse error! Use: go <from> => <to> / <via>".
}}.
Elpi Typecheck.
Elpi Export go.

go source => target / plane.
Fail go nowhere.

(* 
 going from source to target via plane
The command has indeed failed with message:
Parse error! Use: go <from> => <to> / <via>


  Last, (good) Elpi programs should fail reporting intellegible error messages,
  as the previous one. If they just fail, they produce the following generic
  error.

*)
Elpi Command bad.
Elpi Accumulate lp:{{ main []. }}.
Elpi Typecheck.
Elpi Export bad.

Fail bad 1.

(*
The command has indeed failed with message:
The elpi command bad failed without giving a specific error message. Please
report this inconvenience to the authors of the program.
*)