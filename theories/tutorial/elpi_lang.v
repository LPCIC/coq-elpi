
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
   This little tutorial does not talk about Coq, but rather focuses on
   Elpi as a programming language. It assumes no previous knowledge of
   Prolog and λProlog. Coq can be used as an environment for stepping trough
   the tutorial one paragraph at a time. The text between [lp:{{] and [}}] is
   Elpi code, while the rest are Coq directives to drive the interpreter.

   1. Logic programming: unification and backtracking
   2. Higher order features
   3. Modes and constraints
   4. Functional style
   5. Debugging
   
*)

(* ------------------------------------------------ *)
(* Boilerplate, please ignore *)
From elpi Require Import elpi.
Elpi Command tutorial lp:{{
  kind person type.
  type mallory, bob, alice person.
  pred age o:person, o:int.
  pred older o:person, o:person.
}}.
(* End Boilerplate *)
(* ------------------------------------------------ *)

(** ---- 1. Logic programming: unification and backtracking ---- *)

(**
   We start by introducing the first order fragment of
   λProlog, i.e. the terms will not contains binders.

   A λProlog program is made of clauses that declare
   when a predicate holds.

   For example the next commands "accumulates" on top
   of the current "tutorial" program a bunch of clauses describing
   the age of 3 individuals. 
*)

Elpi Accumulate tutorial lp:{{

 age mallory 23.
 age bob 23.
 age alice 20.
 
}}.

(**
   Note about the syntax:
   - Variables are identifiers starting with a capital letter
   - constants (for individuals or predicates) are identifiers
     starting with a lowercase letter

   The entry point of a program is called query,
   i.e. an expression containing variables as

     [age alice A]

   and the execution of the program assigns [A] to the
   age of alice.
*)

Elpi Query tutorial lp:{{
  age alice A, coq.say "The age of alice is" A.
}}.

(**
   [age] is also said to be a relation (in contrast to
   a function), since it computes both ways.
*)

Elpi Query tutorial lp:{{
  age P 23, coq.say P "is 23 years old".
}}.

(**
   A query as [age P 23] is unified with each
   and every clause. Unification compares two
   terms structurally and eventually assigns variables.

   For example for the first clause of the program we obtain
   the following unification problem

     [age P 23 = age mallory 23]

   that is simplified into smaller equations following
   the structure of the terms

     [age = age]
     [P = mallory]
     [23 = 23]

   The second can be satisfied by assigning mallory to [P].
   All equations are solved, hence unification succeeds.
   Note that the [=] sign is part of the syntax.  The query

     [age P 23]

   can be rewritten as

     [A = 23, age P A]

   See also: https://en.wikipedia.org/wiki/Unification_(computer_science)#Syntactic_unification_of_first-order_terms


   The first part of the query is succesful and the rest of
   the query is run: the value of [P] is printed as well as
   the "is 23" string.
*)

(**
   Unification can actually fail.

*)

Elpi Query tutorial lp:{{
  age P 20, coq.say P "is 20".
}}.

(**
   Once again the unification problem for the first clause
   in the program is

     [age P 20 = age mallory 23]

   that is simplified into smaller equations following
   the structure of the terms

     [age = age]
     [P = mallory]
     [20 = 23]

   The second equation assigns [P], but the third one fails.

   When failure occurs, the next clause in the program is
   tried and all assignements are undone, i.e. [P] is fresh again.
   This operation is called backtracking.

   The unification problem for the next clause is:

     [age P 20 = age bob 23]

   This one also fails.  The last one is:

     [age P 20 = age alice 20]

   This one works, and the assigment [P = alice] is kept as the result
   of the first part of the query.

*)

(**
   A query can combine multiple predicates (using [,]) and
   they all have to be satisfied. Here we ask for two distinct
   indivisuals that have the same age.
*)

Elpi Query tutorial lp:{{
  age P A, age Q A, not(P = Q),
  coq.say P "and" Q "are" A "years old".
}}.

(**
   Backtracking is global.  The first solution for
   [age P A] and [age Q A] picks [P] and [Q] to be the same
   individual [mallory], but then [not(P = Q)] fails and
   forces the last choice that was made to be reconsidered,
   so [Q] becomes [bob].

   Look at the outout of the following instrumented code:
*)

Elpi Query tutorial lp:{{
   age P A, age Q A, coq.say "I picked" P "and" Q,
   not(P = Q),
   coq.say "the last choice worked!",
   coq.say P "and" Q "are" A "years old".
}}.

(**
   Clauses may have premises. Here we add to our program
   a clase that defiens what [older P Q] means in terms of
   the [age] of [P] and [Q].
*)
Elpi Accumulate tutorial lp:{{
  older P Q :- age P N, age Q M, N > M.
}}.

(** Let's run a query using older *)

Elpi Query tutorial lp:{{
  older bob X,
  coq.say "bob is older than" X.
}}.

(* The query [older bob X] is unified with the head of
   the program clause [older P Q], assigning [P = bob]
   and [X = Q].  Then new queries are run

     [age bob N]

     [age Q M]

     [N > M]

   The former assigns [N = 23], the second one first
   sets [Q = mallory] and [M = 23].  This makes the last
   query to fail, since [23 > 23] is false.  Hence the
   second query is run again and again until [Q] is
   set to alice and [M] to [20]. 
*)

(**
   Variables in the query are said to be existentially
   quantified because λProlog will try to find one
   possible value for them.

   Conversely, the variables used in clauses are
   universally quantified in the front of the clause.
   This means that the program same clause can be used
   multiple times, and each time the variables are fresh.

   Here the variable [P] in [older P Q :- ...] once takes
   [bob] and another time takes [mallory].
*)

Elpi Query tutorial lp:{{
  older bob X, older mallory X,
  coq.say "bob and mallory are older than" X.
}}.

(** ---- 2. Higher order features ---- *)

(**
   So far the syntax of terms is based on constants
   (eg [age] or [mallory]) and variables (eg [X]).

   λProlog adds to constants another term constructor:
   λ-abstraction (written [x\...]).
  
   Functions build using λ-abstraction can be applied
   to arguments and honor usual the β-reduction rule
   (the argument is substituted for the bound variable).

   In the following example [F 23 reads, once
   the β-reduction is performed, [age alice 23].
*)

Elpi Query tutorial lp:{{
  F = (x\ age alice x),
  F 20, not(F 23).
}}.

(**
   Let's now write the "hello world" of λProlog, an
   interpreter and type checker for the simply
   typed lambda calculus. We call this program "stlc".

   We start by declaring that "term" is a type and
   that "app" and "lam" are constructors of that type.

*)

Elpi Command stlc lp:{{
  kind  term  type.

  type  app   term -> term -> term.
  type  lam   (term -> term) -> term.
}}.

(**
   The constructor "app" takes two terms
   while "lam" only one (of functional type).

   Note that:
   - there is no constructor for variables, we will 
     use the notion of bound variable of λProlog in order
     to represent variable 
   - "lam" takes a function as subterm, i.e. something
     we can build using the λ-abstraction [x\...]

   As a consequence, the identity function is written
     [lam (x\ x)]
   while the "first" function is written
     [lam (x\ lam (y\ x))]

   This approach is called HOAS:
     https://en.wikipedia.org/wiki/Higher-order_abstract_syntax

   Another consequence of this approach is that there is no
   such a thing as a free variable. One can have (global) constants,
   but variable are only available under the λ-abstraction of the
   programming language, that gives them a well defined scope and
   substitution operation (β-reduction).
*)

(**
   We implement weak head reduction, that is we stop reducing
   when the term the is a "lam" or a global constant.

   If the term is [(app (lam F) A)] then we compute the reduct [(F A)].
   Note that [F] is a λProlog function, so passing an argument to it
   implements the subtitution of the actual argument for the bound variable.

   We first give a type and a mode for our predicate [weakhd]. It reads
   "weakhd takes a term in input and gives a term in output". We will
   explain what input means precisely later, for now just think about it
   as a comment.
   
*) 
Elpi Accumulate lp:{{
  pred weakhd i:term, o:term.

  % when the head "Hd" of an "app" (lication) is a "lam" we substitute
  % and continue
  weakhd (app Hd Arg) Reduct :- weakhd Hd (lam F), !,
    weakhd (F Arg) Reduct.

  % otherise a term X is already in normal form.
  weakhd X Reduct :- Reduct = X.
}}.

(** 
   Recall that all clauses are eventually used (unified with the query).
   Here, whenever the first clause applies, we want the second one to be
   skipped. Indeed if the term is [app (lam x\x) t] (for some t) its weak head
   normal form cannot be [app (lam x\x) t] as the second clause suggest.

   The [!] operator discards all alternatives following the current clause.
   It commits to the currently chosen clause for the current query (but leave
   all clauses available for subsequent queries).

   A little test using constants
   
*)
Elpi Accumulate stlc lp:{{
  type foo, bar term.
}}.

Elpi Query stlc lp:{{
  Fst = lam (x\ lam y\ x),
  T = app (app Fst foo) bar,
  weakhd T T1, coq.say "weakhd of T is" T1,
  S = app foo bar,
  weakhd S S1, coq.say "weakhd of S is" S1.
}}.

(** Another test with a lambda term that has no weak head normal form *)
Elpi Bound Steps 1000. (* Let's be cautios *)
Fail Elpi Query lp:{{
  Delta = lam (x\ app x x),
  Omega = app Delta Delta,
  weakhd Omega Hummm, coq.say "not going to happen".
}}.
Elpi Bound Steps -1.

(**
   Remark we have used the binders of λProlog to implement substitution.
   This feature is complemented by the [pi] operator and the [=>] connective
   in order to be able to manipulate terms with binders, in particular to
   recurse under a binder.

   A good showcase for these features is to implement a type checker
   for the simply typed lambda calculus
      See also: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

   We start by defining the data type of simple types and then
   we provide two clauses, one for each term constructor
 *)
Elpi Accumulate stlc lp:{{
  kind  ty   type.           % the data type of types
  type  arr  ty -> ty -> ty. % our type constructor

  pred of i:term, o:ty. % the type checking algorithm

  % for the app node we test the head is a function from
  % A to B, and that the argument is of type A
  of (app Hd Arg) B :-
    of Hd (arr A B), of Arg A.

  % for lambda, instead of using a context (a list) of bound
  % variables we use the pi and => primitives, explained below
  of (lam F) (arr A B) :-
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
   a fixed A (but still not assigned A) and a fresh
   constant x.

   Note that hypothetical clauses are added at the top of the
   program, that is they take precedence over static clauses.
*)

Elpi Query stlc lp:{{
  of (lam (x\ lam y\ x)) Ty, coq.say "The type is" Ty.
}}.

(**
  Let's run step by step this example.

  The clause for lam is used:
  - [Ty] is assigned [(arrow A1 B1)]
  - a fresh [c1] is created by the [pi] construct
  - [of c1 A1] is added to the program by the [=>] construct,
  - the new query of [(lam y\ c1) B1] is run.

  Again, the clause for lam is used (since its variables are
  universally quantified, we use fresh A2, B2... this time):
  - [B1] is assigned [(arrow A2 B2)]
  - a fresh [c2] is created by the [pi] construct
  - [of c2 A2] is added to the program by the [=>] construct,
  - the new query [of c1 B2] is run.

  The (hypotetical) clause [of c1 A1] is used:
  - [B2] gets assigned to [A1]

  The value of [Ty] is hence [(arr A1 (arr A2 A1))], a good type
  for the fst function (the first argument and the output
  have the same type [A1]).

*)

Fail Elpi Query lp:{{
  Delta = lam (x\ app x x),
  of Delta Ty, coq.say "now going to happen".
}}.

(**
  The term [lam (x\ app x x)] is not well typed:

  The clause for lam is used:
  - [Ty] is assigned [(arrow A1 B1)]
  - a fresh [c1] is created by the [pi] construct
  - [of c1 A1] is added to the program by the [=>] construct,
  - the new query [of (app c1 c1) B1] is run.
  The clause for app is used:
  - the query [of c1 (arr A2 B2)] assignes to [A1] the
    value [(arr A2 B2)].  This means that the
    hypothetical clause is now [of c1 (arr A2 B2)].
  - the query [of c1 A2] fails because
    [A2 = (arr A2 B2)] has no solution
*)

(**
   The semantics of a λProlog program is given by interpreting
   it in terms of logical formulas and proof search.

   A clause

     p A B :- q A C, r C B.

   has to be understood as a formula

     ∀A B C, (q A C ∧ r C B) → p A B

   A query is a goal that is proved by backchaining
   clauses.  For example [p 3 X]
   is solved by unifying it with the conclusion of
   the formula above (that sets [A] to [3]) and 
   generating two new queries, [q 3 C] and
   [r C B]. Note that [C] is an argument to both
   [q] and [r] and acts as a link: if solving [q]
   fixes [C] then the query for [r] sees that.
   Similarly for [B], that is identified with [X],
   and is hence a link from the solution of [r] to
   the solution of [p].

   A clause like

     of (lam F) (arr A B) :-
       pi x\ of x A => of (F x) B.

   reads

     ∀F A B, (∀x, of x A → of (F x) B) → of (lam F) (arr A B).

   Hence, "x" and "of x A" are available only
   temporarily to prove  "of (F x) B" and this is
   also why "A" cannot change during this sub proof (A is
   quantified once and forall outside).

   Each program execution is a proof of the query
   and is made of the program clauses seen as axioms.

*)

(** ---- 3. Modes and constraints ---- *)

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

Elpi Command peano lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred add o:nat, o:nat, o:nat.

add (s X) Y (s Z) :- add X Y Z.
add z X X.

}}.

(* It computes! *)

Elpi Query peano lp:{{
  add (s (s z)) (s z) R, coq.say "2 + 1 =" R.
}}.

(* Unfortunately the relation does not work well
   when the first argument is flexible.  Depending on the
   order of the clause can wither diverge or pick
   z as a value for X (that may not be what one wants) *)

Elpi Bound Steps 100.
Fail Elpi Query peano lp:{{ add X (s z) Y }}.
Elpi Bound Steps 0.

(* We can use the mode directive in order to
   match arguments marked as i against the patterns
   in the head of clauses *)

Elpi Command peano2 lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred sum i:nat, i:nat, o:nat.

sum (s X) Y (s Z) :- sum X Y Z.
sum z X X.

}}.

Fail Elpi Query peano2 lp:{{ sum X (s z) Y. }}.

(**
   We can also suspend such goals and turn them into
   syntactic constraints *)

Elpi Accumulate peano2 lp:{{
  sum X Y Z :- var X, declare_constraint (sum X Y Z) [X].
}}.

Elpi Query peano2 lp:{{ sum X (s z) Z, print_constraints. }}.

(**
   Syntactic constraints are resumed when the variable
   they are suspended on is assigned *)

Elpi Query peano2 lp:{{ sum X (s z) Z, X = z, coq.say "The result is:" Z. }}.

Fail Elpi Query peano2 lp:{{ sum X (s z) (s (s z)), X = z. }}.
Elpi Query peano2 lp:{{ sum X (s z) (s (s z)), (X = z ; X = s z). }}.

(* Remark how computation suspends, then makes progess,
   then suspends again... *)

Elpi Query peano2 lp:{{
   sum X (s z) Y, 
   print_constraints,
   X = s Z, 
   print_constraints, 
   Z = z,
   coq.say "Finally:" Y.
}}.

(**
   Sometimes the set of syntactic constraints becomes unsatisfiable
   and we would like to be able to fail early. *)

Elpi Accumulate peano2 lp:{{

pred even i:nat.
pred odd  i:nat.

even z.
even (s X) :- odd X.
odd (s X) :- even X.

odd X :- var X, declare_constraint (odd X) [X].
even X :- var X, declare_constraint (even X) [X].

}}.

Elpi Query peano2 lp:{{ even (s X), odd (s X), print_constraints }}.

(* A rule can see the set of syntactic constraints as a whole,
   and inject new goals, in this case fail *)

Elpi Accumulate peano2 lp:{{

constraint even odd {
  rule (even X) (odd X) <=> 
   (coq.say X "can't be even and odd at the same time", fail).
}

}}.

Fail Elpi Query lp:{{ even (s X), odd (s X) }}.

(** ---- 4. Functional style ---- *)

(**
    Elpi is a relational language. Features typical of functional
    programming are available, at some extent, with some caveats.

    Chaining "relations" can be painful, especially when
    they look like functions. Here we use [std.append]
    and [std.rev] as examples. *)

Elpi Command function lp:{{

pred make-palindrome i:list A, o:list A.

make-palindrome L Result :-
  std.rev L TMP,
  std.append L TMP Result.

pred make-palindrome2 i:list A, o:list A.

make-palindrome2 L Result :-
  std.append L {std.rev L} Result.

}}.

Elpi Query function lp:{{
  make-palindrome [1,2,3] A,
  make-palindrome2 [1,2,3] B,
  coq.say A "=" B.
}}.

(**
   The two programs are equivalent, and indeed the latter is
   elaborated into the former.
   
   Higher order predicates can be used, but one has to be wary
   of where variables are bound. *)

Elpi Command map lp:{{

pred bad i:list int, o:list int.

% Note: pred std.map i:list A, i:(A -> B -> prop), o:list B.
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

Elpi Query map lp:{{
  not(bad [1,2,3] R1),
  good [1,2,3] R2,
  good2 [1,2,3] R3,
  coq.say R2 R3.
}}.

(**
   The problem with [bad] is that [TMP] is fresh each time the clause
   is used, but not every time the anonymous predicate passed to [std.map]
   is used. Technically [TMP] is quantified where [L] and [Result] are.

   There are two ways to quantify [TMP] correctly, that is inside the anonymous
   predicate. One is to actually name the predicate. Another one is
   to use the [sigma] operator to "allocate" [TMP] at every call.
   
   One last way to skin the cat is to use [=>] as follows. *)

Elpi Accumulate map lp:{{

pred good3 i:list int, o:list int.
good3 L Result :-
  (pi TMP X R\ good3.aux X R :- TMP is X + 1, R = TMP) =>
  std.map L good3.aux Result.

}}.

Elpi Query map lp:{{
  good3 [1,2,3] R,
  coq.say R.
}}.

(**
   In this case the auxiliary predicate is only visible inside [good3].
   What is interesting to remark is that the quatifications are explicit
   in the hypothetical clause, and they indicate clearly that each and every
   time it is used [TMP], [X] and [R] are fresh.
   
   The [pi] operator is dual to [sigma]: since here it occurs negatively it
   has the same meaning. *)


(** ---- 5. Debugging ---- *)

(**
   A common λProlog idiom is to have a debug clause
   laying around.  The ":if" attribute can be used to
   make the clause conditionally interpreted (only if the
   given debug variable is set) *)
Elpi Command debug lp:{{
  pred mypred i:int.
  
  :if "DEBUG_MYPRED" mypred X :- coq.say "calling mypred on " X, fail.
  mypred 0 :- coq.say "ok".
  mypred M :- N is M - 1, mypred N.
}}.

Elpi Query debug lp:{{ mypred 3 }}.
Elpi Debug "DEBUG_MYPRED".
Elpi Query debug lp:{{ mypred 3 }}.
Elpi Debug.
Elpi Query debug lp:{{ mypred 3 }}.

(** The Elpi interpreter provides tracing facilities. *)

Elpi Trace.
Elpi Query stlc lp:{{
  of (lam (x\ lam y\ x)) Ty, coq.say Ty.
}}.

(** The trace can be limited to a range of steps (look at the
   numbers near "run = "). *)

Elpi Trace 6 8.
Elpi Query stlc lp:{{
  of (lam (x\ lam y\ x)) Ty, coq.say Ty.
}}.

(* The trace can be limited to a (list of) predicates as follows *)

Elpi Trace "of".
Elpi Query stlc lp:{{
  of (lam (x\ lam y\ x)) Ty, coq.say Ty.
}}.

(** One can combine the range of steps with the predicate *)

Elpi Trace 6 8 "of".
Elpi Query stlc lp:{{
  of (lam (x\ lam y\ x)) Ty, coq.say Ty.
}}.

(** To switch traces off *)

Elpi Trace Off.
 
(**
   One can print the current program to an html file
   excluding some files if needed (extra args
   are regexp on file name, line, clause name) *)
Elpi Print stlc "tutorial.html" "pervasives.elpi".

(**
   Finally, one can bound the number of (resolution) steps
   performed by the interpreter *)
Elpi Query lp:{{ 0 = 0, 1 = 1 }}.
Elpi Bound Steps 1.
Fail Elpi Query lp:{{ 0 = 0, 1 = 1 }}.
Elpi Bound Steps -1. (* Go back to no bound *)

