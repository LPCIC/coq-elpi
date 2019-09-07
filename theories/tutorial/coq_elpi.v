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
   using the "Elpi Program <name> lp:{{ code }}" command. The resulting program
   is obtained by accumulating the code for:

   - built-in predicates (eg "coq.say") and first order terms
     https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

   - higher order terms (eg Coq terms, detailed later in this tutorial)
     https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi

   - the user provided "<code>"

   Later one can accumulate on top of this other clauses
   via "Elpi Accumulate".

   The more specific commands "Elpi Command" and "Elpi Tactic" take "<code>"
   from predefined templates, respectively:

   - https://github.com/LPCIC/coq-elpi/blob/master/elpi-command.elpi
   - https://github.com/LPCIC/coq-elpi/blob/master/elpi-tactic.elpi
   
   The "Elpi Accumulate ..." family of commands lets one accumulate clauses
   taken from:
   
   - verbatim text "Elpi Accumulate lp:{{ <code> }}"
   - text files "Elpi Accumulate File <path>"
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

  main []     :- coq.say "hello world".

  main [str Name] :- coq.say "hello" Name ", you are" {age Name}.

}}.
Elpi Typecheck. (* We will detail later what this is for *)

(** The entry point for commands is "main" that receives a list of
    arguments. See https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi
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
  happens to be a possible qualified name) or terms (always between parentheses).
*)

Elpi Command arguments.
Elpi Accumulate lp:{{

  main Arguments :-
    coq.say "Arguments: " Arguments.

}}.
Elpi Typecheck.
Elpi arguments "argument1" argum.ent2 3 (3).


(** 
   Elpi comes with a type checker. It is invoked any time
   a query is run by hand via "Elpi Query", or when invoked via
   "Elpi Typecheck".
   It is not run when a comment/tactic in invoked via its main entry point.
*)
Elpi Command illtyped.
Elpi Accumulate lp:{{
  pred test o:bool.
  test (tt ^ "3").
}}.
Fail Elpi Typecheck illtyped.

(** ----------------------- HOAS for Gallina ----------------------------- *)

(** 
     The full syntax of Coq terms can be found here

        https://github.com/LPCIC/coq-elpi/blob/master/coq-HOAS.elpi

     Let's start with the "gref" data type and the "global" term
     constructor.
     
     The "coq.locate" builtin resolves a name to a global rerence ("gref").

      type const @constant -> gref.
      type indt @inductive -> gref.
      type indc @constructor -> gref.

     "@constant", "@inductive" and "@constructor" are Coq specific data
     types that are opaque to Elpi. Still the "gref" data type lets you
     see what these names point to (a constant, and inductive type or a
     constructor). By convention opaque data types' name starts with "@".
*)
Elpi Command global_references.
Elpi Query lp:{{
  coq.locate "nat" GRnat,   coq.say "nat is:" GRnat,
  coq.locate "S" GRs,       coq.say "S is:" GRs,
  coq.locate "plus" GRplus, coq.say "plus is:" GRplus.
}}.

(**
   The "coq.env.*" family of built-in predicates lets one access the
   environment of well typed Coq terms that have a global name.
   *)

Definition x := 2.

Elpi Query lp:{{

  coq.locate "x" GR,
  coq.env.typeof-gr GR Ty, % all global references have a type
  coq.say "The type of x is:" Ty,

  GR = const C, % destruct GR to obtain its @constant part C
  coq.env.const C Bo Ty, % constans have body (and a type, the same as before)
  coq.say "The body of x is:" Bo

}}.

(**
    Remark: "indt «nat»" is not a term (or better a type).
    The "global" term constructor turns a "gref" into an actual term.

    type global gref -> term. 

    Remark: the "app" term constructor taking a list of terms an building
    the application. "app [global (indc «S»), global (indc «O»)]" is
    the representation of 1.

    type app   list term -> term.

    Let's move to binders!
*)

Definition f := fun x : nat => x.

Elpi Query lp:{{

  coq.locate "f" (const C),
  coq.env.const C Bo _,
  coq.say "The body of f is:" Bo

}}.

(**
   The "fun" constructor carries a pretty printing hint "`x`", the type
   of the bound variable "nat" and a function describing the body:

     type fun  @name -> term -> (term -> term) -> term.
   
   Remark: @name is just for pretty printing, in spite of carrying
   a value in the Coq world, then have no semantical meaning in Elpi. *)

Elpi Query lp:{{ fun `foo` T B = fun `bar` T B }}.
  
(**
   Other binders "prod" (Coq's "forall", AKA "Π") and "let" are similar,
   so let's rather focus on "fix" here.
*)

Elpi Query lp:{{

  coq.locate "plus" (const C),
  coq.env.const C Bo _,
  coq.say "The body of plus is:" Bo

}}.

Check match 3 as w in nat return bool with 0 => true | S _ => false end.

(**
   The "fix" constructor carries a pretty printing hint, the number of the
   recursive argument (starting at 0), the type and finally the body where the
   recursive call is represented via a bound variable

     type fix   @name -> int -> term -> (term -> term) -> term.

   A "match" constructor carries the term being inspected, the return clause
   and a list of branches. Each branch is a Coq function expecting in input
   the arguments of the corresponding constructor. The order follows the
   order of the constructors in the inductive type declaration.

     type match term -> term -> list term -> term.

   The return clause is represented as a Coq function expecting in input
   the indexes of the inductive type, the inspected term and generating the
   type of the branches.
*)

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
match h as e in eq _ x return P 0 -> P x with eq_refl => fun (p : P 0) => p end.

Elpi Query lp:{{

    coq.locate "m" (const C),
    coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
    coq.say "The return type of m is:" RT
  
}}.
  

(**
   The last term constructor worth discussing is "sort".

   type sort  universe -> term.

   type prop universe.
   type typ @univ -> universe.
   
   The opaque @univ is a universe level variable. Elpi holds a store of
   constraints among these variable and provides built-in predicates to
   impose constraints named "coq.univ.*".
*)

Elpi Query lp:{{

  coq.univ.sup U U1,
  coq.say U "<" U1,
  not(coq.univ.leq U1 U) % This constraint can't be allowed in the store!

}}.

(**
    Note that the user is not required to declare universe constraints by hand,
    since the type checking primitives update the store of constraints
    automatically and put Coq universe variables in place of Elpi's unification
    variables (U and V below).
*)

Elpi Query lp:{{

  ID = (fun `x` (sort (typ U)) x\ x),
  A = (sort (typ U)), % the same U as before
  B = (sort (typ V)),
  coq.say "(id b) is:" (app [ID, B]),
  not(coq.typecheck (app [ID, A]) T), % since U : U is not valid
  coq.typecheck (app [ID, B]) T,      % since V : U is possible
  coq.say "(id b) is now:" (app [ID, B]) ":" T, % remark: U and V are now Coq's
  coq.univ.print                                % @univ with constraints

}}.

(** --------------- Quotations and Antiquotations ------------------------- *)

(**
   Writing Galling terms as we did so far is surely possible but very verbose
   and unhandy. Elpi provides a system of quotations and antiquotations to
   let one take advantage of the Coq parser to write terms.
   
   The antiquotation, from Coq to Elpi, is written lp:{{ .. }} and we have
   been using it since the beginning of the tutorial. The quotation from
   Elpi to Coq is written {{:coq .. }} or also just {{ .. }} since the ":coq" is
   the default quotation. (Coq has no default quotation, hence you always need
   to write "lp:" there).
*)

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
   One rule governs bound variables: 
    
     if a variable is bound in language X
     then the variable is only visible in language X.
   
   The following example is horrible but proves this point. In real code
   you are encouraged to pick appropriate names for your variables, avoiding
   gratuitous (visual) clashes.
*)

Elpi Query lp:{{

  coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:{{ x }} }})
%                          e         c          c         e
}}.

(**
   A commodity quotation without parentheses is provided for identifiers,
   that is "lp:{{ <ident> }}" can be written just "lp:<ident>".
*)


Elpi Query lp:{{

  coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:x }})
%                          e         c          c      e
}}.

(**
   Since it is quite frequent to put Coq variables in the scope of an Elpi
   unification variable, a shorhand for "lp:{{ X {{a}} {{b}} }}" is provided
   in the form of "lp:(X a b)".
    
   Note that writin "lp:X a b" (without parentheses) would result in a
   Coq application, not an Elpi one. *)

Elpi Query lp:{{

  X = (x\y\ {{ lp:y + lp:x }}),
  coq.say {{ fun a b : nat => lp:(X a b) }}

}}.
    
(**
    A last commodity quotation lets one access the "coqlib"
    feature introduced in Coq 8.10.
    
    Coqlib gives you an indirection between your code and the actual name
    of constants.

    Remark: the optional "@" to disable implicits. *)

Register Coq.Init.Datatypes.nat as my.N.
Register Coq.Init.Logic.eq as my.eq.

Elpi Query lp:{{

  coq.say {{ fun a b : lib:my.N => lib:@my.eq lib:my.N a b }}

}}.

(**
    Implicit arguments are not synthesized automatically
    when quotations are used. It is the job of the elaborator
    to synthesize them.
*)

Elpi Query lp:{{

  T = (fun `ax` {{nat}} a\ {{ fun b : nat => lp:a = b }}),
  coq.say "before:" T,
  % this is the standard Coq elaborator (but you may write your own ;-)
  coq.elaborate T _ T1,
  coq.say "after:" T1.

}}.
     
(** -------------------- Usecase: Synthesizing a term ---------------------- *)

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


(** ------------------------ Usecase: Solving a goal ----------------------- *)

(** XXXXXXX   Warning: this part of coq-elpi is experimental.    XXXXXXXX *)

(**
   In Coq a proof is just a term, and an incomplete proof is just a term
   with holes standing for the open goals.

  When a proof starts there is just one hole (one goal) and its type
  is the statement one wants to prove. Then proof construction makes
  progress by instantiation: a term possibly containing holes is
  grafted to the hole corresponding to the current goal. What a tactic
  does behind the scenes is to synthesize this partial term.

  While the entry point for commands is "main" then one for tactics
  is called "solve". Tactics written in Elpi can be invoked via the
  "elpi" tactic.

  Let's define a simple tactic that prints the current goal.
*)

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve _ [goal Ctx Proof Type _] _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type,
    coq.say "Proof state:",
    coq.sigma.print.

}}.

Elpi Typecheck.
Lemma tutorial x y  : x + 1 = y.
Proof.
elpi show.
Abort.

(**

  In the Elpi code up there "Proof" is the hole for the current goal,
  "Type" the statement to be proved and "Ctx" the proof context. Since we
  don't assign "Proof" the tactic makes no progess. Elpi prints something
  like this:

   [decl c0 `x` (global (indt «nat»)), decl c1 `y` (global (indt «nat»))] 
   |- X0 c0 c1 : 
     app
      [global (indt «eq»), global (indt «nat»), 
       app
        [global (const «Nat.add»), c0, 
         app [global (indc «S»), global (indc «O»)]], c1]

  The first line is the proof context, and is a list of variables declarations.
  Proof variables are bound Elpi variables (here "c0" and "c1"), the context is
  a list of predicates holding on them. For example

    decl c0 `x` (global (indt «nat»))

  asserts that "c0" (pretty printed as "`x`") has type "nat".

  Then we see that the value of "Proof" is "X0 c0 c1". This means that the
  proof of the current goal is represented by Elpi's variable "X0" and that
  the variable has "c0" and "c1" in scope (the proof can use them).

  Finally we see find the type of the goal "x + 1 = y".

  After that Elpi prints the proof state. The proof state is the collection of
  goals together with their types. In the side of Elpi this state is represented
  by constraints for the "evar" predicate.

   {c0 c1} :
   decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
   ?- evar (X0 c0 c1) 
       (app
         [global (indt «eq»), global (indt «nat»), 
          app
           [global (const «Nat.add»), c0, 
            app [global (indc «S»), global (indc «O»)]], c1]) (X1 c0 c1)  /* suspended on X0, X1 */

  One can recognize the set of bound variables "{c0 c1}", the hypothetical
  context of clauses about them (that also corresponds to the proof context),
  and finally the suspended query "evar (X0 c0 c1) .. (X1 c0 c1)".

  The set of constraints on "evar" represents the Coq data structure called
  "sigma" (hence the name of the built-in to print it) that is used to
  represent the proof state in Coq. It is printed just afterwards:

   ...
   sigma =
    EVARS:
     ?X16==[x y |- x + 1 = y] (goal evar) {?Goal}
   ...
   Coq-Elpi mapping:
     ?X16 <-> X1

  The last part is a bijection between Coq's existential variables (AKA evars)
  and Elpi's unification variables. Coq uses the evar ?X16 in the example above
  to represent the (missing) proof of the goal. On the Elpi side X1 plays that
  role.

  One last thing to explain is why in Elpi the variable used to represent the
  goal is X0 while the one to represent the proof is X1. The meaning of the
  "evar" Elpi predicate linking the two is that the term assigned to the
  former has to be elaborated to the latter, that is the actual proof of the
  goal, when read back in Coq, should be a well typed term. This means that
  when an Elpi tactic  assigns a value to X0 some procedure to turn that
  value into X1 is resumed. That procedure is called elaborator. A possible
  implementation is via the coq.elaborate built-in. An alternative one is
  the "of" predicate implemented in 
  https://github.com/LPCIC/coq-elpi/blob/master/engine/elaborator.elpi
    
  Given this set up, it is impossible to use a term of the wrong type as a
  proof.
*)

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve _ [goal _ Proof _ _] _ :- Proof = {{0}}.
  solve _ [goal _ Proof _ _] _ :- Proof = {{I}}.
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
   Moreover the head of a clause about solve is matched against the
   goal: this operation cannot assign unification variables
   in the goal, only variables in the clause's head. As a consequence
   the following clause for "solve" only triggers when the statement
   features an explicit conjunction.
*)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve _ [goal C Proof {{ lp:A /\ lp:B }} _] GL :-
  Proof = {{ conj lp:PA lp:PB }},
  G1 = goal C PA A _,
  G2 = goal C PB B _,
  GL = [ G1, G2 ].
}}.
Elpi Typecheck.

Lemma fast_path : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split.
all: elpi blind.
Show Proof.
Qed.

(**
   Remark: in the third case the type checking constraint
   on Proof succeeds, i.e. "of" internally unifies the type of the given term
   with the goal. In this case instantiating the statement of the goal to
   "nat" fails because "t" is a "Prop", so it picks "I".


    Let's implement Ltac's match goal with.

    Ltac provides a special syntactic construct to inspect
    a goal called "match goal with ... end".

    It is easy to implement it in Elpi since it is made of two components:
    - a first order matching procedure (no unfolding)
    - non-determinism to "pair" hypotheses and patterns for the context.

    The first ingredient is the standard "copy" predicate.
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
  (std.forall PHyps p\ std.exists Hyps h\ pmatch-hyp h p),
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

(** Let's now extract higher order terms from the context, like the
   predicate about "y" *)

Elpi Accumulate lp:{{

pred context-of i:term, i:term, o:(term -> term).
context-of What Where F :- pi x\ (copy What x) => copy Where (F x).

pred constant? i:(A -> B).
constant? F :- pi x y\ F x = F y.

solve _ [(goal Ctx E ETy _ as G)] _ :- % [nabla x\ goal _ (Ng x) _ _] :-
  pattern-match G (with [decl _X _NameX Ty] T (context-of T Ty C, not(constant? C))),
  E = {{let ctx := fun y => lp:(C y) in lp:(Ng ctx) }}.
}}.
Elpi Typecheck.

Lemma ltac2 x (H : exists y, x <> 0 /\ y = x) : x <> 0 .
Proof.
elpi tutorial.ltac.
change (ctx (x<>0)) in H.
Abort.
