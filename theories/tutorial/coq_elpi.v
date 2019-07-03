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

(**
   This tutorial focuses on the integration of Elpi within Coq.
   This tutorial assumes the reader is familiar with Elpi and HOAS; if it is not
   the case, please take a look at this other tutorial first:
     https://github.com/LPCIC/coq-elpi/blob/master/theories/tutorial/elpi_lang.v
   
   - Coq Programs: Commands, Tactics and Db
   - HOAS for Gallina
   - Quotations and Antiquotations
   - Usecase: Synthesizing a term
   - Usecase: Solving a goal
   
*)


(** ------------------------- Defining commands ---------------------------- *)


(**
   In the previous tutorial we have seen that an Elpi program can be declared
   using the "Elpi Program <name> lp:{{code}}" command. The resulting program
   is obtained by accumulating the code for built-in predicates (eg "coq.say",
   see 
     https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi), built-in
   data types (eg Coq terms, 
     https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi
   detailed later in this tutorial) and finally the
   user provided "<code>". Later one can accumulate on top of this other clauses
   via "Elpi Accumulate".

   The more specific commands "Elpi Command" and "Elpi Tactic" take "<code>"
   from predefined templates:
     https://github.com/LPCIC/coq-elpi/blob/master/elpi-command.elpi
   and
     https://github.com/LPCIC/coq-elpi/blob/master/elpi-tactic.elpi
   respectively.

   The "Elpi Accumulate ..." command lets one accumulate cleases taken from
   verbatim text,
     "Elpi Accumulate lp:{{ ... }}"
   text files,
     "Elpi Accumulate File <path>"
   or data bases (Db)
     "Elpi Accumulate Db <name>"

   A "Db" can be create with
     "Elpi Db <name> <code>"
   and can be later extended via "Elpi Accumulate". A "Db" is pretty much
   like regular program but can be shared among other programs (A program
   accumulates a Db by name, not by contents). 

   Let's define a Db.
  *)

Elpi Db age.db lp:{{ % We like Db to be named using a .db suffix

  % A typical Db is made of one main predicate
  pred age o:string, o:int.

  % the Db is empty for now, we put a clase giving a descriptive error
  % and we name it "age.fail".
  :name "age.fail"
  age Name _ :- coq.error "I don't know who" Name "is!".

}}.

(**
   Elpi clauses can be given a name via the ":name" attribute. Named clauses
   serve as anchor-points when clauses are added to the Db.

   Let's define a Command that makes use of a Db.

   The entry point for commands is "main" that receives a list of
   arguments. See https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi
   for their constructors/types. *)

Elpi Command tutorial.
Elpi Accumulate Db age.db.
Elpi Accumulate lp:{{

  main []     :- coq.say "hello world".

  main [str Name] :- coq.say "hello" Name ", you are" {age Name}.

}}.
Elpi Typecheck. (* We will detail later what this is for *)

(** The entry point for commands is "main" that receives a list of
    arguments. See https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi
    for their constructors/types.

    Elpi provides a syntax to call (query) the standard entry point of tactics
    and commands.
*)

Elpi tutorial.           (** Elpi Query tutorial lp:{{ main [] }} *)
Fail Elpi tutorial bob.  (** Elpi Query tutorial lp:{{ main [str "bob"] }} *)

(**
   Let's put some data in the Db. Given that the Db contains a catch-all clause,
   we need to new one to be put before it. *)

Elpi Accumulate age.db lp:{{

  :before "age.fail"
  age "bob" 24.

}}.

Elpi tutorial bob.

(** Elpi programs, like Dbs, are open ended: they can
    be extended later on by accumulating extra code. The same consideration
    about named clauses as anchor point and the :before attribute apply. *)
Elpi Accumulate tutorial lp:{{

  main _ :- coq.say "usage: tutorial [name]". 

}}.
Elpi tutorial "too" "many" "args".

(** 
   Elpi comes with a type checker. It is invoked any time
   a query is run by hand via "Elpi Query", or when invoked via
   "Elpi Typecheck".
   It is not invoken when a comment/tactic in ivoked via its corresponding
   entry point. *)
Elpi Command illtyped.
Elpi Accumulate lp:{{
  pred test o:boo.
  test (tt ^ "3").
}}.
Fail Elpi Typecheck illtyped.

(** ----------------------- HOAS for Gallina ----------------------------- *)

(** 
     The full syntax of Coq terms can be found here
        https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi

     Let's start with the "gref" data type and the "global" term
     constructor.
     
     Thq "coq.locate" builtin resolve a name to a global rerence.

      type const @constant -> gref.
      type indt @inductive -> gref.
      type indc @constructor -> gref.

     "@constant", "@inductive" and "@constructor" are Coq specific data
     types that are opque to Elpi. Still the "gref" data type lets you
     see what these names point to (a constant, and inductive type or a
     constructor). By convention opaque data types' name starts with "@"
*)
Elpi Command global_references.
Elpi Query lp:{{
  coq.locate "nat" GRnat,   coq.say "nat is" GRnat,
  coq.locate "S" GRs,       coq.say "S" GRs,
  coq.locate "plus" GRplus, coq.say "plus is" GRplus.
}}.

(**
   The "coq.env." family of built-in predicates let's one access the 
   environment of terms of Coq.
   *)

Definition x := 2.

Elpi Query lp:{{

  coq.locate "x" GR,
  coq.env.typeof-gr GR Ty, % all global references have a type
  coq.say "The type of x is" Ty,

  GR = const C,
  coq.env.const C Bo Ty, % constans have body and a type
  coq.say "The body of x is" Bo

}}.

(**
    Remark that "indt «nat»" is not a term (or better a type).
    The "global" term constructor turns a "gref" into an actual term.

    type global gref -> term. 

    Remark the "app" term constructor taking a list of terms an building
    the application. "app [global (indc «S»), global (indc «O»)]" is
    the representation of 1.

    type app   list term -> term.

    Let's move to binders. 
*)

Definition f := fun x : nat => x.

Elpi Query lp:{{

  coq.locate "f" (const C),
  coq.env.const C Bo _,
  coq.say "The body of f is" Bo

}}.

(**
   The "lam" constructor carries a pretty printing hint "`x`", the type
   of the bound variable "nat" and a function describing the body:

     type lam  @name -> term -> (term -> term) -> term.
   
   Remark that @name is just for pretty printing, in spite of carrying
   a value in the Coq world, then have no semantical meaning in Elpi. *)

Elpi Query lp:{{ lam `foo` T B = lam `bar` T B }}.
  
(** Other binders "prod" and "let" are similar. Let's focus on "fix" *)

Elpi Query lp:{{

  coq.locate "plus" (const C),
  coq.env.const C Bo _,
  coq.say "The body of plus is" Bo

}}.

(**
   The "fix" constructor carries a pretty printing hint, the number of the
   recursive argument starting at 0, and the type and the body where the
   recursive call is represented via a bound variable

     type fix   @name -> int -> term -> (term -> term) -> term.

   A "match" constructor carries the term being inspected, the return clause
   and a list of branches. Each branch is a Coq function expecting in input
   the arcguments of the corresponding constructor.

   The return clause is represented as a Coq function expecting in input
   the indexes of the inductive type, the inspected term and generating the
   type of the branches.  
   

   The last term constructor worth discussing is "sort".

   type sort  universe -> term. % Prop, Type@{i}

   type prop universe.
   type typ @univ -> universe.
   
   The opaque @univ is a universe level variable. Elpi holds a store of
   constraints among these variable and provides built-in predicates to
   impose constraints.
*)

Elpi Query lp:{{

  coq.univ.sup U U1,
  coq.say U "<" U1,
  not(coq.univ.leq U1 U) % This constraint can't be allowed in the store!

}}.

(**
    Note that the user is not required to declare universe constraints by hand,
    since the type checking primitives update the store of constraints
    automatically. *)

Elpi Query lp:{{
  coq.univ.new [] U,
  ID = (lam `x` (sort (typ U)) x\ x),
  A = (sort (typ U)),
  B = (sort (typ V)),
  not(coq.typecheck (app [ID, A]) T),
  coq.typecheck (app [ID, B]) T,
  coq.say ID A B.

}}.

(** --------------- Quotations and Antiquotations ------------------------- *)

(**
   Writing Galling terms as we did so far is surely possible but very verbose
   and unhandy. Elpi provides a system of quotations and antiquotations to
   let one use the Coq parser to write terms. The antiquotation, from Coq to
   Elpi, is written lp:{{..}} and we have been using it since the beginnig
   of the tutorial. The quotation from Elpi to Coq is written {{:coq ..}} or
   also just {{..}} since the ":coq" is the default quotation. (Coq has no
   default quotation, hence you always need to write "lp:" there. *)

Elpi Query lp:{{

  coq.say {{:coq 1 + 2 }} "=" {{ 1 + 2 }}

}}.

(** Of course quotation can nest. *)

Elpi Query lp:{{

  coq.locate "S" S,
  coq.say {{ 1 + lp:{{ app[global S, {{ 0 }} ]  }}   }}
% elpi....  coq..     epi............  coq  elpi  coq
}}.

(**
   One rule governs bound variables: if a variable's binder
   is in language X then the variable is only visible in language X.
   
   The following example is horrible but proves this point. In real code
   you are encouraged to pick appropriate names for your variables, avoiding
   gratuitous (visial) clashes. *)

Elpi Query lp:{{

  coq.say (lam `x` {{nat}} x\ {{ fun x : nat => x + lp:{{ x }} }})
%                          e         c          c         e
}}.

(** A commodity quotation without parentheses is provided for lp:{{<ident>}} *)


Elpi Query lp:{{

  coq.say (lam `x` {{nat}} x\ {{ fun x : nat => x + lp:x }})
%                          e         c          c      e
}}.

(** Since it is quite frequent to put Coq variables in the scope of an Elpi
    unification variable, a shorhand for lp:{{ X {{a}} {{b}} }} is provided.
    
    Note that writin lp:X a b would result in a Coq application, not an Elpi
    one. *)

Elpi Query lp:{{

  X = (x\y\ {{ lp:y + lp:x }}),
  coq.say {{ fun a b : nat => lp:(X a b) }}

}}.
    
(** Last a commodity quotation is provided for accessing the "coqlib"
    feature introduced in Coq 8.10.
    
    Coqlib gives you an indirection between your code and the actual name
    of constans.

    Remark the optional "@" to disable implicits. *)

Register Coq.Init.Datatypes.nat as elpi.tutorial.N.
Register Coq.Init.Logic.eq as elpi.tutorial.eq.

Elpi Query lp:{{

  coq.say {{ fun a b : lib:elpi.tutorial.N =>
                lib:@elpi.tutorial.eq lib:elpi.tutorial.N a b }}
}}.

(** Implicit arguments are not synthesized automatically
    when quotations are used. Implicits are represented by a special
    term constructor called "hole". It is the job of the elaborator
    to synthesize them. *)

Elpi Query lp:{{

  T = {{ fun a b : nat => a = b }},
  coq.say "before" T,
  % this is the standard Coq elaborator (but you may write your own ;-)
  coq.elaborate T T1 _,
  coq.say "after" T1

}}.
     
(** -------------------- Usecase: Synthesizing a term ---------------------- *)

(**
   Synthesizing a term typically involves reading an existing declaration
   and writing a new one. The relevant APIs are in
     https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
   in the coq.env.* namespace and are named after the global refence
   they manipulate, eg coq.env.const for reading and coq.env.add-const for
   writing.

   Hee we implement a little command that given an inductive type
   generates a term of type nat whose value is the number of constructors
   of the inductive type. *)

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
    coq.env.add-const Name Nnat hole _ _. % save it
}}.
Elpi Typecheck.

Elpi constructors_num "bool" "nK_bool".
Print nK_bool. (* number of constructor of "bool" *)


(** ------------------------ Usecase: Solving a goal ----------------------- *)

(** Warning: this part of coq-elpi is experimental. *)

(**
   TODO:
   - tactic by instantiation
   - HOAS of evars
     - of + declare-evar constraints

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

*)

(** 
   While the entry point for commands is "main" then one for tactics
   is called "solve". Like "main", "solve" gets a list of arguments,
   but also a list of goals and is expected to return a list of new goals.
   
   We define a tactic called "show" *)

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve Arguments [goal Ctx Evar Type _Attribues] _ :-
    coq.say "Goal:" Ctx "|-" Evar ":" Type,
    coq.say "Elpi proof state:", coq.evd.print,
    coq.say "Arguments: " Arguments.

}}.
Elpi Typecheck.

(**
   Tactics can be invoked via the "elpi" tactic. Arguments can either be
   strings (no double quote needed if the string happens to be
   an possible qualified name) or terms (always between parentheses) *)

Lemma tutorial x y : x + 1 = y -> True.
Proof.
elpi show "argument1" argument2 3 (x + y) x (x).
Abort.

(**
   This blind tactic trie *)

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve _ [goal _ Evar _ _] _ :- Evar = {{0}}.
  solve _ [goal _ Evar _ _] _ :- Evar = {{I}}.
}}.
Elpi Typecheck.

Lemma tutorial : True * nat.
Proof.
split.
- elpi blind.
- elpi blind.
Qed.

(**
   Elpi's equality on ground (evar free) Coq terms corresponds to
   alpha equivalence.

   The head of a clause about solve is matched against the
   goal: this operation cannot assign unification variables
   in the goal, only variables in the clause's head. *)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve _ [goal C Evar {{ lp:A /\ lp:B }} _] GLS :-
    coq.say Evar,
    Evar = {{ conj lp:E1 lp:E2 }},
    GLS = [goal C E1 A _, goal C E2 B _],
    print_constraints, coq.say GLS.
}}.
Elpi Typecheck.

Lemma fast_path : exists t, True /\ True /\ t.
Proof.
eexists.
repeat elpi split.
all: elpi blind.
Qed.

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

Elpi Tactic tutorial.ltac.
Elpi Accumulate lp:{{

kind goal-pattern type.
type with @goal-ctx -> term -> prop -> goal-pattern.
pred pattern-match i:goal, o:goal-pattern.
pred pmatch i:term, o:term.
pred pmatch-hyp i:prop, o:prop.

:name "pmatch:syntactic"
pmatch T P :- copy T P.

% If one asks for a decl, we also find a def
pmatch-hyp (decl X N Ty)    (decl X N PTy) :- pmatch Ty PTy.
pmatch-hyp (def X N Ty _ _) (decl X N PTy) :- pmatch Ty PTy.
pmatch-hyp (def X N Ty B _) (def X N PTy PB _) :- pmatch B PB, pmatch Ty PTy.

% We first match the goal, then we see if for each hypothesis pattern
% there exists a context entry that matches it, finally we test the condition.
pattern-match (goal Hyps _ Type _) (with PHyps PGoal Cond) :-
  pmatch Type PGoal,
  (std.forall PHyps p\ std.exists Hyps h\ pmatch-hyp h p), % forall and exists are in lp-lib
  Cond.

solve _ [(goal _ E _ _ as G)] _ :-
  pattern-match G (with [decl X NameX T,decl Y NameY T] T (not(X = Y))),
  coq.say "Both" NameX "and" NameY "solve the goal, picking the first one",
  E = X.

}}.
Elpi Typecheck.

Lemma ltac1 (x y : bool) (H : x = y) (H0 : y = y) (H1 := H) (H2 : x = x) : x = y.
Proof. 
elpi tutorial.ltac.
Qed.

(* Let's now extract higher order terms from the context, like the
   predicate about "y" *)

Elpi Accumulate lp:{{

pred pierce i:term, o:term.
pierce T PT :- (copy hole _ :- !) => copy T PT.

pred context-of i:term, i:term, o:(term -> term).
context-of What Where F :- pi x\ (copy What x) => copy Where (F x).

pred constant? i:(A -> B).
constant? F :- pi x y\ F x = F y.

solve _ [(goal Ctx E ETy _ as G)] _ :-
  pattern-match G (with [decl _X _NameX Ty] T (context-of T Ty C, not(constant? C))),
  Ctx => std.spy(of {{let ctx := fun y => lp:(C y) in _}} ETy E).
}}.
Elpi Typecheck.

Lemma ltac2 x (H : exists y, x <> 0 /\ y = x) : x <> 0 .
Proof.
elpi tutorial.ltac.
change (ctx (x<>0)) in H.
Abort.
