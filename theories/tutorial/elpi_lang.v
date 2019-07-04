From elpi Require Import elpi.

(**
   Elpi is an extension language that comes as a library
   to be embedded into host applications such as Coq.

   Elpi is a variant of λProlog enriched with constraints. 
   λProlog is a programming language designed to make it easy
   to manipulate abstract syntax trees containing binders.
   Elpi extends λProlog with modes and constraints in order
   to make it easy to manipulate abstract syntax trees
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
   This little tutorial does not talk about Coq, but rather focuses on
   Elpi as a programming language. It assumes no previous knowledge of
   Prolog and λProlog. Coq can be used as an environment for stepping trough
   the tutorial one paragraph at a time. The text between "lp:{{" and "}}" is
   Elpi code, while the rest are Coq directives to drive the interpreter.

   - Logic programming: unification and backtracking
   - Higher order features
   - Modes and constraints
   - Functional style & bindings
   - Debugging
   - Further reading

*)

(** ------------ Logic programming: unification and backtracking ----------- *)

(**
   We start by introducing the first order fragment of
   λProlog, i.e. the terms will not contains binders.

   Our first program (a Command in Coq's jargon) is called "tutorial".

   We begin by declaring the (typed) signature of our terms.
   Here we declare that "person" is a type, and that
   "mallory", "bob" and "alice" are terms of that type.
*)

Elpi Program tutorial lp:{{

  kind person  type.
  type mallory, bob, alice person.

}}.

(**
   A λProlog program is made of clauses that declare
   when a predicate holds. Clauses are accumulated one after the
   other into a program. 

   The next commands accumulates on top
   of the current "tutorial" program a predicate declaration for "age"
   and 3 clauses representing our knowledge about our terms.
   
   Note that "int" is the primitive data type of integers.
*)

Elpi Accumulate lp:{{

  pred age o:person, o:int.

  age mallory 23.
  age bob 23.
  age alice 20.
 
}}.

(**
   The predicate "age" has two arguments, the former is a person while
   the latter is an integer. The label "o:" (standing for "output")
   is a mode declaration and are explained later on, for now they can be
   ignored.

   Now that we have a program we can run it!

   The entry point of a program is called a query,
   i.e. a predicate expression containing variables such as

     "age alice A"

   and the execution of the program is expected to assign to "A" the
   age of alice.

   Note about the syntax:
   - Variables are identifiers starting with a capital letter, eg
     A, B, FooBar, Foo_bar, X1
   - constants (for individuals or predicates) are identifiers
     starting with a lowercase letter, eg
     foo, bar, this_that, camelCase, dash-allowed, qmark_too?, arrows->as_well

  A query can be composed of many predicate expressions linked by ","
  that stands for conjunction: we want to get an answer to all of the
  predicate expressions.

  "coq.say" is a built-in predicate provided by coq-elpi.
  It takes any arguments and prints them.
  Built-in predicates are documetned in the following file:
    https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

*)

Elpi Query lp:{{

  age alice A, coq.say "The age of alice is" A

}}.

(**
   Note that "strings" are also a primitive data type.

   "age" is said to be a relation (in contrast to
   a function), since it computes both ways: we can as
   Elpi which person "P" is 23 years old.
*)

Elpi Query lp:{{

  age P 23, coq.say P "is 23 years old"

}}.

(**
   Operationally, query as "age P 23" is unified with each
   and every clause present in the program starting from the first one.
   
   Unification compares two
   terms structurally and eventually assigns variables.

   For example for the first clause of the program we obtain
   the following unification problem

     "age P 23 = age mallory 23"

   that is simplified into smaller equations following
   the structure of the terms

     "age = age"

     "P = mallory"

     "23 = 23"

   The second can be satisfied by assigning mallory to "P".
   All equations are solved, hence unification succeeds.
   Note that the "=" sign is a regular predicate. Indeed the query

     "age P 23"

   can be rewritten as

     "A = 23, age P A"

   See also
     https://en.wikipedia.org/wiki/Unification_(computer_science)#Syntactic_unification_of_first-order_terms


   The first part of the query is succesful and the rest of
   the query is run: the value of "P" is printed as well as
   the "is 23 years old" string.

   Let's try a query harder to solve.

*)

Elpi Query lp:{{

  age P 20, coq.say P "is 20 years old"

}}.

(**
   This time the unification problem for the first clause
   in the program is

     "age P 20 = age mallory 23"

   that is simplified into smaller equations following
   the structure of the terms

     "age = age"

     "P = mallory"

     "20 = 23"

   The second equation assigns "P", but the third one fails.

   When failure occurs, the next clause in the program is
   tried and all assignements are undone, i.e. "P" is fresh again.
   This operation is called backtracking.

   The unification problem for the next clause is:

     "age P 20 = age bob 23"

   This one also fails.  The last one is:

     "age P 20 = age alice 20"

   This one works, and the assigment "P = alice" is kept as the result
   of the first part of the query.

   An even harder query is the following one whee we ask for two distinct
   indivisuals to have the same age.
*)

Elpi Query lp:{{

  age P A, age Q A, not(P = Q),
  coq.say P "and" Q "are" A "years old"

}}.

(**
   This example shows that backtracking is global.  The first solution for
   "age P A" and "age Q A" picks "P" and "Q" to be the same
   individual "mallory", but then "not(P = Q)" fails and
   forces the last choice that was made to be reconsidered,
   so "Q" becomes "bob".

   Look at the outout of the following instrumented code:
*)

Elpi Query lp:{{

   age P A, age Q A, coq.say "I picked" P "and" Q,
   not(P = Q),
   coq.say "the last choice worked!",
   coq.say P "and" Q "are" A "years old"

}}.

(**
   The clauses we have seen so far are facts: they always hold.
   In general clauses can have premises, that is conditions necessary in
   order to make the predicate hold.
   
   Here we add to our program a clase that defiens what "older P Q" means
   in terms of the "age" of "P" and "Q". Note that ">" is a built-in predicate.
*)
Elpi Accumulate lp:{{

  pred older o:person, o:person.
  older P Q :- age P N, age Q M, N > M.

}}.

(** Let's run a query using older *)

Elpi Query lp:{{

  older bob X,
  coq.say "bob is older than" X

}}.

(**
   The query "older bob X" is unified with the head of
   the program clause "older P Q" (what is to the left of ":-"),
   assigning "P = bob" and "X = Q".  Then new queries are run:

     "age bob N"

     "age Q M"

     "N > M"

   The former assigns "N = 23", the second one first
   sets "Q = mallory" and "M = 23".  This makes the last
   query to fail, since "23 > 23" is false.  Hence the
   second query is run again and again until "Q" is
   set to alice and "M" to "20". 

   Variables in the query are said to be existentially
   quantified because λProlog will try to find one
   possible value for them.

   Conversely, the variables used in clauses are
   universally quantified in the front of the clause.
   This means that the same program clause can be used
   multiple times, and each time the variables are fresh.

   Here the variable "P" in "older P Q :- ..." once takes
   "bob" and another time takes "mallory".
*)

Elpi Query lp:{{

  older bob X, older mallory X,
  coq.say "bob and mallory are older than" X

}}.

(** ---------------------- Higher order features --------------------------- *)

(**
   So far the syntax of terms is based on constants
   (eg "age" or "mallory") and variables (eg "X").

   λProlog adds to constants another term constructor:
   λ-abstraction (written "x\..."). The variable name
   before the \ can be capital as well: given that it is
   expliclty bound Elpi needs not to guess if it is a global
   symbol or a clause variable (that required the convention of
   using capitals for variables).
  
   Functions build using λ-abstraction can be applied
   to arguments and honor the usual β-reduction rule
   (the argument is substituted for the bound variable).

   In the following example "F 23" reads, once
   the β-reduction is performed, "age alice 23".
*)

Elpi Query lp:{{

  F = (x\ age alice x),
  coq.say "F =" F,
  coq.say "F 20 =" (F 20),
  coq.say "F 23 =" (F 23)

}}.

(**
   Let's now write the "hello world" of λProlog: an
   interpreter and type checker for the simply
   typed lambda calculus. We call this program "stlc".

   We start by declaring that "term" is a type and
   that "app" and "fun" are constructors of that type.

*)

Elpi Program stlc lp:{{

  kind  term  type.

  type  app   term -> term -> term.
  type  fun   (term -> term) -> term.

}}.

(**
   The constructor "app" takes two terms
   while "fun" only one (of functional type).

   Note that:
   - there is no constructor for variables, we will 
     use the notion of bound variable of λProlog in order
     to represent variables
   - "fun" takes a function as subterm, i.e. something
     we can build using the λ-abstraction "x\..."

   As a consequence, the identity function is written

     "fun (x\ x)"

   while the "first" function is written

     "fun (x\ fun (y\ x))"

   Another consequence of this approach is that there is no
   such a thing as a free variable. One can have (global) constants,
   but variables are only available under the λ-abstraction of the
   programming language, that gives them a well defined scope and
   substitution operation (β-reduction).

   This approach is called HOAS:
     https://en.wikipedia.org/wiki/Higher-order_abstract_syntax

   We can now implement weak head reduction, that is we stop reducing
   when the term the is a "fun" or a global constant (potentially applied).

   If the term is "(app (fun F) A)" then we compute the reduct "(F A)".
   Note that "F" is a λProlog function, so passing an argument to it
   implements the subtitution of the actual argument for the bound variable.

   We first give a type and a mode for our predicate "whd". It reads
   "whd takes a term in input and gives a term in output". We will
   explain what input means precisely later, for now just think about it
   as a comment.
   
*) 
Elpi Accumulate lp:{{

  pred whd i:term, o:term.

  % when the head "Hd" of an "app" (lication) is a "fun" we substitute
  % and continue
  whd (app Hd Arg) Reduct :- whd Hd (fun F), !,
    whd (F Arg) Reduct.

  % otherise a term X is already in normal form.
  whd X Reduct :- Reduct = X.

}}.

(** 
   Recall that, due to backtracking, all clauses are potentially used.

   Here, whenever the first premise of the first clause applies,
   we want the second clase to be skipped, since we found a redex (that is not
   in weak head normal form). 

   The premises of a clause are run in order, and the "!" operator discards all
   alternative clauses following the current one. Said otherwise it commits to
   the currently chosen clause for the current query (but leaves
   all clauses available for subsequent queries).

*)

Elpi Query lp:{{

  I = (fun x\x),
  whd I T, coq.say "λx.x ~>" T,
  whd (app I I) T1, coq.say "(λx.x) (λx.x) ~>" T1

}}.

(**

   Another little test using global constants:
   
*)
Elpi Accumulate lp:{{

  type foo, bar term.

}}.

Elpi Query lp:{{

  Fst = fun (x\ fun y\ x),
  T = app (app Fst foo) bar,
  whd T T1, coq.say "(Fst foo bar) ~>" T1,
  S = app foo bar,
  whd S S1, coq.say "(foo bar) ~>" S1

}}.

(**
   A last test with a lambda term that has no weak head normal form
*)
Elpi Bound Steps 1000. (* Let's be cautios *)
Fail Elpi Query lp:{{

  Delta = fun (x\ app x x),
  Omega = app Delta Delta,
  whd Omega Hummm, coq.say "not going to happen"

}}.
Elpi Bound Steps 0.

(**
   Remark we have used the binders of λProlog to implement substitution.
   This feature is complemented by the "pi" operator and the "=>" connective
   in order to be able to recurse under a binder.

   A good showcase for these features is to implement a type checker
   for the simply typed lambda calculus.
   See also https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

   We start by defining the data type of simple types.
   We then declare a new predicate "of" (for type of) and finally
   we provide two clauses, one for each term constructor.
 *)
Elpi Accumulate lp:{{

  kind  ty   type.           % the data type of types
  type  arr  ty -> ty -> ty. % our type constructor

  pred of i:term, o:ty. % the type checking algorithm

  % for the app node we test the head is a function from
  % A to B, and that the argument is of type A
  of (app Hd Arg) B :-
    of Hd (arr A B), of Arg A.

  % for lambda, instead of using a context (a list) of bound
  % variables we use the pi and => primitives, explained below
  of (fun F) (arr A B) :-
    pi x\ of x A => of (F x) B.

}}.

(**
   "pi <name>\ <code>" is a reserved syntax, as well as
   "<code> => <code>".
   Operationally "pi x\ code" introduces a fresh
   constant x and then runs code.
   Operationally "clause => code" adds "clause" to 
   the program and runs code.  Such extra clause is
   said to be hypothetical.
   Both "x" and "clause" are removed once "code" terminates.

   Note that the hypothetical clause is "of x A" for
   a fixed A and a fresh constant x.

   Note that hypothetical clauses are added at the top of the
   program, that is they take precedence over static clauses.
*)

Elpi Query lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say "The type of Fst is:" Ty

}}.

(**
  Let's run step by step this example.

  The clause for fun is used:
  - "Ty" is assigned "(arrow A1 B1)"
  - a fresh constant "c1" is created by the "pi" construct
  - "of c1 A1" is added to the program by the "=>" construct,
  - the new query of "(fun y\ c1) B1" is run.

  Again, the clause for fun is used (since its variables are
  universally quantified, we use fresh A2, B2... this time):
  - "B1" is assigned "(arrow A2 B2)"
  - a fresh "c2" is created by the "pi" construct
  - "of c2 A2" is added to the program by the "=>" construct,
  - the new query "of c1 B2" is run.

  The (hypotetical) clause "of c1 A1" is used:
  - "B2" gets assigned to "A1"

  The value of "Ty" is hence "(arr A1 (arr A2 A1))", a good type
  for the fst function (the first argument and the output
  have the same type "A1").

*)

Fail Elpi Query lp:{{

  Delta = fun (x\ app x x),
  of Delta Ty, coq.say "now going to happen"

}}.

(**
  The term "fun (x\ app x x)" is not well typed:

  The clause for fun is used:
  - "Ty" is assigned "(arrow A1 B1)"
  - a fresh "c1" is created by the "pi" construct
  - "of c1 A1" is added to the program by the "=>" construct,
  - the new query "of (app c1 c1) B1" is run.
  The clause for app is used:
  - the query "of c1 (arr A2 B2)" assignes to "A1" the
    value "(arr A2 B2)".  This means that the
    hypothetical clause is now "of c1 (arr A2 B2)".
  - the query "of c1 A2" fails because
    "A2 = (arr A2 B2)" has no solution
*)

(**
   The semantics of a λProlog program is given by interpreting
   it in terms of logical formulas and proof search.

   A clause

     p A B :- q A C, r C B.

   has to be understood as a formula

     ∀A B C, (q A C ∧ r C B) → p A B

   A query is a goal that is proved by backchaining
   clauses.  For example "p 3 X"
   is solved by unifying it with the conclusion of
   the formula above (that sets "A" to "3") and 
   generating two new queries, "q 3 C" and
   "r C B". Note that "C" is an argument to both
   "q" and "r" and acts as a link: if solving "q"
   fixes "C" then the query for "r" sees that.
   Similarly for "B", that is identified with "X",
   and is hence a link from the solution of "r" to
   the solution of "p".

   A clause like

     of (fun F) (arr A B) :-
       pi x\ of x A => of (F x) B.

   reads, as a logical formula:

     ∀F A B, (∀x, of x A → of (F x) B) → of (fun F) (arr A B)

   or using the inference rule notation typically used for type systems

      𝚪, of x A ⊦ of (F x) B     x fresh
     ------------------------------------
      𝚪 ⊦ of (fun F) (arr A B)

   Hence, "x" and "of x A" are available only
   temporarily to prove  "of (F x) B" and this is
   also why "A" cannot change during this sub proof (A is
   quantified once and forall outside).

   Each program execution is a proof of the query
   and is made of the program clauses seen as axioms.

*)

(** ---------------------- Modes and constraints --------------------------  *)

(**
   Elpi extends λProlog with syntactic constraints
   and rules to manipulate the set of constraints.

   Syntactic constraints are goals suspended on
   a variable and are resumed as soon as such variable
   gets instantiated.

   A companion facility is the declaration of modes.
   The argument of a predicate can be marked as input
   to avoid it being instantiated when unifying the
   the goal with the head of a clause.

   A simple example: Peano's addition *) 

Elpi Program peano lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred add o:nat, o:nat, o:nat.

add (s X) Y (s Z) :- add X Y Z.
add z X X.

}}.

Elpi Query lp:{{

  add (s (s z)) (s z) R, coq.say "2 + 1 =" R

}}.

(**
   Unfortunately the relation does not work well
   when the first argument is a variable.  Depending on the
   order of the clauses for add Elpi can either diverge or pick
   z as a value for X (that may not be what one wants) *)

Elpi Bound Steps 100.
Fail Elpi Query lp:{{ add X (s z) Y }}.
Elpi Bound Steps 0.

(**
   Indeed the first clause for add can be applied forever.
   If one exchanges the two clauses in the program, then Elpi
   terminates picking z for X.

   We can use the mode directive in order to
   match arguments marked as i against the patterns
   in the head of clauses *)

Elpi Program peano2 lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred sum i:nat, i:nat, o:nat.

sum (s X) Y (s Z) :- sum X Y Z.
sum z X X.

}}.

Fail Elpi Query lp:{{ sum X (s z) Y }}.

(**
   Instead of failing we can suspend goals and turn them into
   syntactic constraints *)

Elpi Accumulate lp:{{

sum X Y Z :-
  % this clause always applies, we double check X is a variable
  var X,
  % then we declare the constraint and trigger its resumption of the
  % assignment of X
  declare_constraint (sum X Y Z) [X].
  
}}.

Elpi Query lp:{{ sum X (s z) Z, print_constraints }}.

(**
   Syntactic constraints are resumed when the variable
   they are suspended on is assigned *)

Elpi Query lp:{{

  sum X (s z) Z, X = z,
  coq.say "The result is:" Z,
  print_constraints % prints nothing

}}.

(**
    A couple more examples:
    - resumption can cause failure
    - ";" stands for disjunction
*)

Fail Elpi Query lp:{{ sum X (s z) (s (s z)), X = z }}.
Elpi Query lp:{{ sum X (s z) (s (s z)), (X = z ; X = s z) }}.

(** Remark how computation suspends, then makes progess,
   then suspends again... *)

Elpi Query lp:{{
  
   sum X (s z) Y, 
   print_constraints, coq.say "Currently Y =" Y,
   X = s Z, 
   print_constraints, coq.say "Currently Y =" Y,
   Z = z,
   coq.say "Finally Y =" Y

}}.

(**
   Sometimes the set of syntactic constraints becomes unsatisfiable
   and we would like to be able to fail early. *)

Elpi Accumulate lp:{{

pred even i:nat.
pred odd  i:nat.

even z.
even (s X) :- odd X.
odd (s X) :- even X.

odd X :- var X, declare_constraint (odd X) [X].
even X :- var X, declare_constraint (even X) [X].

}}.

Elpi Query lp:{{ even (s X), odd (s X), print_constraints }}.

(**
   A constraint (handling) rule can see the set of syntactic constraints
   as a whole, remove constraints and/or create new goals *)

Elpi Accumulate lp:{{

constraint even odd {
  % if two distinct, conflicting, constraints about the same X
  % are part of the store
  rule (even X) (odd X) <=> 
   % generate the following goal
   (coq.say X "can't be even and odd at the same time", fail).
}

}}.

Fail Elpi Query lp:{{ even (s X), odd (s X) }}.

(**
   See also
     https://en.wikipedia.org/wiki/Constraint_Handling_Rules
   for an introduction to the sub language to manipualte constraints.
*)

(** ------------------- Functional style ---------------------------------- *)

(**
    Elpi is a relational language, not a functional one. Still some features
    typical of functional programming are available, with some caveats.
    
    First, functions about built-in data types are available via the infix "is"
    predicate *)

Elpi Query lp:{{  X is 3 + 2, Y is "result " ^ "=", coq.say Y X }}.

(**
    Chaining "relations" can be painful, especially when
    they look like functions. Here we use "std.append"
    and "std.rev" as examples. *)

Elpi Program function lp:{{

% Note that variables (capital letters) can be used in
% types in order to describe ML-like polymorphism.
pred make-palindrome i:list A, o:list A.

make-palindrome L Result :-
  std.rev L TMP,
  std.append L TMP Result.

pred make-palindrome2 i:list A, o:list A.

make-palindrome2 L Result :-
  std.append L {std.rev L} Result.

}}.

Elpi Query lp:{{

  % Note that list is a primitive data type with syntax
  % - [] for nil
  % - [Hd | Tail] for cons
  % - [ E1, E2 | Tail ] for iterated cons, where | Tail can be omitted if the
  %   list is nil terminated
  make-palindrome [1,2,3] A,
  make-palindrome2 [1,2,3] B,
  coq.say A "=" B

}}.

(**
   The two programs are equivalent, and indeed the latter is
   elaborated into the former. Expression between {} are
   said to be spilled out and placed just before the predicate
   that constains them. 
   
   The "calc" predicate is just a wrapper around the infix "is" *)

Elpi Query lp:{{ coq.say "result =" {calc (2 + 3)} }}.

(**
   Higher order predicates can be defined, but one has to be wary
   of where variables are bound. *)

Elpi Accumulate lp:{{

pred bad i:list int, o:list int.

% Note that the standard library declares
%   pred std.map i:list A, i:(A -> B -> prop), o:list B.
% Remark "prop" is the type of predicates and that the type
% of "std.map" declared by the "pred" directive is
%   type std.map list A -> (list A -> list B -> prop) -> list B -> prop
% Indeed "pred" extends a type declaration (for predicates, hence the trailing
% -> prop is implicit) with a mode declaration for each argument.
bad L Result :-
  std.map L (x\ r\ TMP is x + 1, r = TMP) Result.

pred good i:list int, o:list int.
good L Result :-
  std.map L good.aux Result.
good.aux X R :- TMP is X + 1, R = TMP.

pred good2 i:list int, o:list int.
good2 L Result :-
  std.map L (x\ r\ sigma TMP\ TMP is x + 1, r = TMP) Result.

}}.

Elpi Query lp:{{

  not(bad [1,2,3] R1),
  good [1,2,3] R2,
  good2 [1,2,3] R3,
  coq.say R2 R3

}}.

(**
   The problem with "bad" is that "TMP" is fresh each time the clause
   is used, but not every time the anonymous predicate passed to "std.map"
   is used. Technically "TMP" is quantified (allocated) where "L" and "Result"
   are.

   There are two ways to quantify "TMP" correctly, that is inside the anonymous
   predicate. One is to actually name the predicate. Another one is
   to use the "sigma" operator to allocate "TMP" at every call.
   
   One last way to skin the cat is to use "=>" as follows. It gives us
   the occasion to clarify further the scope of variables. *)

Elpi Accumulate lp:{{

pred good3 i:list int, o:list int.
good3 L Result :-
  (pi TMP X R\ good3.aux X R :- TMP is X + 1, R = TMP) =>
  std.map L good3.aux Result.

}}.

Elpi Query lp:{{

  good3 [1,2,3] R,
  coq.say R

}}.

(**
   In this case the auxiliary predicate is only visible inside "good3".
   What is interesting to remark is that the quatifications are explicit
   in the hypothetical clause, and they indicate clearly that each and every
   time good3.aux is used "TMP", "X" and "R" are fresh.
   
   The "pi" operator is dual to "sigma": since here it occurs negatively it
   has the same meaning.

   The last remark worth making is that bound variables are intimately related
   to universal quantification, while unification variables are related to
   existential quantification.  It goes without saying that the the following
   two queries are not equivalent and while the former is trivial the latter
   is false: 
     
     ∀x, ∃Y, Y = x   
     ∃Y, ∀x, Y = x
*)

Elpi Query lp:{{ pi x\ sigma Y\ Y = x }}.
Fail Elpi Query lp:{{ sigma Y\ pi x\ Y = x }}.

(** 
   Another way to put it: x is in the scope of Y only in the first formula,
   hence x can be assigned to Y in that case only.

   More in general, λProlog tracks the bound variables that are in scope of each
   unification variable. There are only two ways to put a bound variable
   in the scope: 
   - quantify the unification variable under the bound one (first formula)
   - pass the bound variable to the unification variable explicitly: in this
     the case the unification variable needs to have a functional type.
     Indeed ∃Y, ∀x, (Y x) = x has a solution: Y can be the identity function.

   If we look again at the clause for type checking
   lambda abstraction

     of (fun F) (arr A B) :-
       pi x\ of x A => of (F x) B.

   we can read the scopes (recall all unification variables such as F A B are
   quantified upfront). The only unification variable that sees the fresh
   x is F, because we pass x to F explicitly. Indeed when we write

      𝚪, x : A ⊦ f : B
    --------------------
      𝚪 ⊦ λx.f : A → B

   on paper, the x being bound can only occur in f (not in 𝚪 or B for example).
   Reamrk that in the premise x is still bound, this time not by a λ but by the
   context 𝚪, x : A. In λProlog the context is the set of hypothetical clauses
   and pi-quantified variables and is implicitly handled by the runtime of the
   programming language.
   
   A slogan to keep in mind is that
     "there is not such as thing as a free variable"
  and indeed the variable bound by the lambda abstraction (of our data) is
  replaced by a fresh variable bound by the context (of our program). This is
  called binder mobility. See also https://hal.inria.fr/hal-01884210/
  
*)

(** ---------------------------- Debugging --------------------------------- *)

(**
   A common λProlog idiom is to have a debug clause
   laying around.  The ":if" attribute can be used to
   make the clause conditionally interpreted (only if the
   given debug variable is set) *)
Elpi Program debug lp:{{

  pred mypred i:int.
  
  :if "DEBUG_MYPRED" mypred X :- coq.say "calling mypred on " X, fail.
  mypred 0 :- coq.say "ok".
  mypred M :- N is M - 1, mypred N.

}}.

Elpi Query lp:{{ mypred 3 }}.
Elpi Debug "DEBUG_MYPRED".
Elpi Query lp:{{ mypred 3 }}.
Elpi Debug.
Elpi Query lp:{{ mypred 3 }}.

(**
   As a slightly more sophisticated debugging feature, the Elpi interpreter
   provides tracing facilities. *)

Elpi Trace.
Elpi Query stlc lp:{{ % We run the query in the stlc program

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.
Fail Elpi Query stlc lp:{{

  of (fun (x\ app x x)) Ty, coq.say Ty

}}.

(**
   The trace can be limited to a range of steps. Look at the
   numbers "run HERE {{{". *)

Elpi Trace 6 8.
Elpi Query stlc lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

(**
   The trace can be limited to a (list of) predicates as follows *)

Elpi Trace "of".
Elpi Query stlc lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

(** One can combine the range of steps with the predicate *)

Elpi Trace 6 8 "of".
Elpi Query stlc lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say Ty
  
}}.

(** To switch traces off *)

Elpi Trace Off.
 
(**
   Given that programs are not written in a single place, but rather obtained by
   accumulating code, Elpi is able to print a (full) program to an html file
   as follows. The obtained file provides a facility to filter clauses by their
   predicate. *)
Elpi Print stlc "tutorial.html".

(**
   Finally, one can bound the number of backchaining steps
   performed by the interpreter *)
Elpi Query lp:{{ 0 = 0, 1 = 1 }}.
Elpi Bound Steps 1.
Fail Elpi Query lp:{{ 0 = 0, 1 = 1 }}. (* it needs more than 1 step! *)
Elpi Bound Steps 0. (* Go back to no bound *)

(** ----------------------- Further reading -------------------------------- *)

(**

  The website
    http://www.lix.polytechnique.fr/~dale/lProlog/
  contains useful links to λProlog related material.

  Papers and other documentation about Elpi can be found at
    https://github.com/LPCIC/elpi/

  A tutorial specific to Elpi as an extension language for Coq
  can be found in the
         https://github.com/LPCIC/coq-elpi/blob/master/theories/tutorial/coq_elpi.v
  file.

*)


