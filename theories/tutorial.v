(* ---------------------------------------------- *)
(* Table of contents:
   - Coq: its functional programming languae and
     the syntax of its terms
   - λProlog: a programming language designed to
     manipulate syntax trees containing binders
  
*)

(* ---------------------------------------------- *)
(* Coq provides a functional programming language *)

Inductive Tree :=
  | Leaf (n : nat)
  | Node (l : Tree) (r : Tree).

Definition sum_tree :=
  fix sum (t : Tree) : nat := 
    match t with
    | Leaf n => n
    | Node l r => sum l + sum r
    end.

Eval compute in
  sum_tree (Node (Leaf 3) (Node (Leaf 4) (Leaf 0))).

(* Let's dig into the term syntax *)

Check sum_tree. (* Tree -> nat *)
Print sum_tree. (*

fix sum (t : Tree) : nat :=
  match t with
  | Leaf n => n
  | Node l r => sum l + sum r
  end

*)

(* in CoqIDE SHIFT-ALT-L *)
Set Printing All.
Check sum_tree.  (* forall _ : Tree, nat *)
Print sum_tree.  (*

fix sum (t : Tree) : nat :=
  match t return nat with
  | Leaf n => n
  | Node l r => Nat.add (sum l) (sum r)
  end

*)

(* A lot of syntactic sugar. E.g. Notations *)
Locate "_ -> _".
Locate "_ + _".

(* Even more sugar (as of today, no real low
   level printer):

fix sum {struct 1} (forall _ : Tree, nat) :=
  fun (t : Tree) =>
    match t return (fun _ : Tree => nat) with
    | Leaf =>
        fun (n : nat) => n
    | Node =>
        fun (l : Tree) =>
        fun (r : Tree) =>
          Nat.add (sum l) (sum r)
  end

  The {struct 1} annotation tells Coq that the
  recursive function sum is defined by structural
  recursion on its first (an only) argument.  In Coq
  recusrive functions have to terminate, only structural
  recursion is allowed.

  The branches of the pattern match construct are functions
  taking in input the arguments of the constructor.

  The return annotation to match is a function to the
  type of each branch given the term being scrutinized.
  This is peculiar to the type system of Coq, where
  branches can have related, but different, types.
  In this case they are all of type nat (the tree is ignored).

*)

(* To sum up, Coq provides a functional programming language.
   While the concrete syntax is quite rich, the bare bones terms
   are built from:
   - constants (Nat.add, Leaf, Tree, nat)
   - pattern matching 
   - fixpoints (structurally recursive functions)
   - lambda abstraction (fun)
   - function application (juxtaposition)

   Plus the following ones, not visible in this example:
   - sorts (Type, Prop)
   - let-in (local definition)
   - type casts (typing annotations) 


   Manipulating Coq terms in OCaml is quite combersome.

   Bound variables are represented by De Bruijn indexes:
   the term `Nat.add (sum l) (sum r)` is internally
   written
     `App ("Nat.add", [App("sum",[Rel 2]);
                       App("sum",[Rel 1])])`
   since the binder for `l` is at distance 2, while
   the binder for `r` is at distance 1.  When binders
   are added or removed these indexes have to be
   adjusted, and this activity is error prone.  Still
   De Bruijn indexes solve important problems as
   α-conversion and capture avoiding substitution.
   More info at: https://en.wikipedia.org/wiki/De_Bruijn_index


   The objective of coq-elpi is to provide a scripting
   language for Coq that is better suited to express the
   manipulation of terms with binders.  This language is
   the object of the rest of this tutorial.
*)


(* ------------------------------------------------ *)
(* Boilerplate, please ignore *)
From elpi Require Import elpi.
Elpi Init "./" "./elpi/".
Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate "
type coq-say A -> prop.
coq-say A :- $coq-say A.
kind person type.
type mallory person.
type alice person.
type bob person.
".
(* End Boilerplate *)

(* Elpi is an embedded λProlog interpreter.
   λProlog is a programming language designed to
   manipulate syntax trees containing binders.

   coq-elpi, this software, is embedding elpi
   in Coq as a scripting language.

   In CoqIDE please chose "coq-elpi" in

     Edit -> Preferences -> Colors

   to have proper syntax highlight of the
   following text.
*)

(* 
   We begin by introducing the first order fragment of
   λProlog, i.e. the terms will not contains binders.
   We then introduce the constructs to deal with binders.



   A λProlog program is made of clauses that declare
   when a predicate holds.

   For example the next commands "accumulates" on top
   of the current program a bunch of clauses describing
   the age of 3 individuals.
*)

Elpi Accumulate "
 age mallory 23.
 age bob 23.
 age alice 20.
".

(* Note about the syntax:
   - Variables are identifiers starting with a capital letter
   - constants (for individuals or predicates) are identifiers
     starting with a lowercase letter

   The entry point (main) of a program is a query,
   i.e. an expression containing variables as
     `age alice X`
   and the execution of the program assigns X to the
   age of alice.
*)
Elpi Run "
  age alice A, coq-say ""Alice is "", coq-say A.
".

(* `age` is also said to be a relation (in contrast to
   a function), since it `computes` both ways.
*)

Elpi Run "
  age P 23, coq-say P, coq-say "" is 23"".
".

(* A query as `age P 23` is unified with each
   and every clause. Unification compares two
   terms structurally and eventually assigns variables.

   For example for the first clause of the program we obtain
   the following unification problem

     age P 23 = age mallory 23

   that is simplified into smaller equations following
   the structure of the terms

     age = age
     P = mallory
     23 = 23

   The second can be satisfied by assigning mallory to P.
   All equations are solved, hence unification succeeds.
   Note that the = sign is part of the syntax.  The query

     age P 23

   can be rewritten as
     
     A = 23, age P A

   See also: https://en.wikipedia.org/wiki/Unification_(computer_science)#Syntactic_unification_of_first-order_terms


   The first part of the query is succesful and the rest of
   the query is run: the value of P is printed as well as
   the "is 23" string.

   What happens when unification fails?

*)

Elpi Run "
  age P 20, coq-say P, coq-say "" is 20"".
".

(* Once again the unification problem for the first clause
   in the program is

     age P 20 = age mallory 23

   that is simplified into smaller equations following
   the structure of the terms

     age = age
     P = mallory
     20 = 23

   The second equation assigns P, but the third one fails.

   When failure occurs, the next clause in the program is
   tried and all assignements are undo, i.e. P is fresh again.
   This operation is called backtracking.

   The unification problem for the next clause is:

     age P 20 = age bob 23

   This one also fails.  The last one is:

     age P 20 = age alice 20

   This one works, and the assigment P = alice is kept as the result
   of the first part of the query.

*)

Elpi Run "age P A, age Q A, not(P = Q),
          coq-say P, coq-say ""and"", coq-say Q, coq-say ""are"", coq-say A
".

(* Backtracking is global.  The first solution for
   age P A and age Q A are the same, but then not(P = Q),
   by failing when both P and Q are mallory, forces the last
   choice that was made to be reconsidered, so Q becomes bob.

   Look at the outout of the following instrumented code:
*)

Elpi Run "age P A, age Q A, coq-say ""attempt"", coq-say P, coq-say Q,
          not(P = Q),
          coq-say ""the last one worked!"",
          coq-say P, coq-say ""and"", coq-say Q, coq-say ""are"", coq-say A
".

(* Clauses may have premises, for example older P Q
   requires the age of P to be greater than the age of Q. *)
Elpi Accumulate "
  older P Q :- age P N, age Q M, N > M.
".

(* Let's run a query using older *)

Elpi Run "older bob X, coq-say ""bob is older than"", coq-say X.".

(* The query older bob X is unified with the head of
   the program clause older P Q, assigning P = bob
   and X = Q.  Then new queries are run
     age bob N
     age Q M
     N > M
   The former assigns N = 23, the second one first
   sets Q = mallory and M = 23.  This makes the last
   query to fail, since 23 > 23 is false.  Hence the
   second query is run again and again until Q is
   set to alice and M to 20. 
*)

(* Variables in the query are said to be existentially
   quantified because λProlog will try to find one
   possible value for them.

   Conversely, the variables used in clauses are
   universally quantified in the front of the clause.
   This means that the program same clause can be used
   multiple times, and each time the variables are fresh.
*)

(* So far the syntax of terms is based on constants
   (eg age or mallory) and variables (eg X).

   λProlog adds to that λ-abstraction
   (written x\...) to build functions.  Such
   functions, when applied, honor the β-reduction
   rule.

   In the following example F 23 reads, once
   the β-reduction is performed, age alice 23.
*)
Elpi Run "
  F = (x\ age alice x),
  F 20, not(F 23).
".

(* Let's write the hello world of λProlog, an
   interpreter and type checker for the simply
   typed lambda calculus.

   Elpi's implementation of λProlog is untyped:
   types play no role in computation.  Still one
   can give type annotations, to improve readability
   and to gide the elpy type checker to find simple
   mistakes.

*)

Elpi Accumulate "
  kind  term  type.
".

(* "term" is a new data type.  We then give
   two term constructors: "app" and "lam".
   We also give their types, "app" takes two terms
   while "lam" only one (of functional type).
*)

Elpi Accumulate "
  type  app   term -> term -> term.
  type  lam   (term -> term) -> term.
".

(* Note that:
   - there is no constructor for variables, we will 
     use the notion of bound variable of λProlog
   - "lam" takes a function as subterm, i.e. something
     we can build using the λ-abstraction x\...

   The identity function is hence written
     lam (x\ x)
   While the "fst" function is written
     lam (x\ lam y\ x)

   This approach is called HOAS:
     https://en.wikipedia.org/wiki/Higher-order_abstract_syntax
*)

(* The interpreter performs weak head reduction, i.e. it stops when
   the terms is a "lam" (or a constant).
   The the term is (app (lam F) A) then it computes the reduct (F A).
   Note that F is a λProlog function, so passing an argument to it
   implements the subtitution of the actual argument for the bound variable.
*) 
Elpi Accumulate "
  whd (app Hd Arg) Reduct :- whd Hd (lam F), whd (F Arg) Reduct.
  whd X X. % a term X is already in normal form.
".

(* A little test using constants *)
Elpi Run "
  Fst = lam (x\ lam y\ x),
  T = app (app Fst foo) bar,
  whd T T1, coq-say T1,
  S = app foo bar,
  whd S S1, coq-say S1.
".

(* A better test... ;-) *)
Fail Timeout 1 Elpi Run "
  Delta = lam (x\ app x x),
  Omega = app Delta Delta,
  whd Omega Hummm, coq-say ""not going to happen"".
".

(* Let's rule out this nasty omega with a type system.
   See also: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
 *)
Elpi Accumulate "
  kind  ty   type.           % the data type of types
  type  arr  ty -> ty -> ty. % our type constructor

  % for the app node we test the head is a function from
  % A to B, and that the argument is of type A
  of (app Hd Arg) B :-
    of Hd (arr A B), of Arg A.

  % for lambda, instead of using a context (a list) of bound
  % variables we use the pi and => primitives, explained below
  of (lam F) (arr A B) :-
    pi x\ of x A => of (F x) B.
".

(* "pi <name>\ <code>" is a reserved syntax, as well as
   "<code> => <code>".
   Operationally "pi x\ code" introduces a fresh
   constant x and then runs code.
   Operationally "clause => code" adds "clause" to 
   the program and runs code.  Such extra clause is
   said to be hypothetical.
   Both x and `clause` are removed once code terminates.

   Note that the hypothetical clause is "of x A" for
   a fixed A (but still not assigned A) and a fresh
   constant x.
*)

Elpi Run "
  of (lam (x\ lam y\ x)) Ty, coq-say Ty.
".

(* Let's run step by step this example.

  The clause for lam is used:
  - Ty is assigned (arrow A1 B1)
  - a fresh c1 is created by the pi construct
  - of c1 A1 is added to the program by the => construct,
  - the new query of (lam y\ c1) B1 is run.

  Again, the clause for lam is used (since its variables are
  universally quantified, we use new A2, B2... instead):
  - B1 is assigned (arrow A2 B2)
  - a fresh c2 is created by the pi construct
  - of c2 A2 is added to the program by the => construct,
  - the new query of c1 B2 is run.

  The (hypotetical) clause of c1 A1 is used:
  - B2 gets assigned to A1

  The value of Ty is hence (arr A1 (arr A2 A1)), a good type
  for the fst function (the first argument and the output
  have the same type A1).

*)

Fail Elpi Run "
  Delta = lam (x\ app x x),
  of Delta Ty, coq-say Ty.
".

(* The term `lam (x\ app x x)` is not well typed:

  The clause for lam is used:
  - Ty is assigned (arrow A1 B1)
  - a fresh c1 is created by the pi construct
  - of c1 A1 is added to the program by the => construct,
  - the new query of (app c1 c1) B1 is run.
  The clause for app is used:
  - the query of c1 (arr A2 B2) assigned to A1 the
    value (arr A2 B2).  This means that the
    hypothetical clause is now of c1 (arr A2 B2).
  - the query of c1 A2 fails because
    A2 = (arr A2 B2) has no solution
*)

(* The semantics of a λProlog program is given by interpreting
   it in terms of logical formulas and proof search.

   A clause
     p A B :- q A C, r C B.
   has to be understood as a formula
     ∀A B C, (q A C /\ r C B) => p A B

   A query is a goal that is proved by backchaining
   clauses.  For example `p 3 X`
   is solved by unifying it with the conclusion of
   the formula above (that sets A to 3) and 
   generating two new queries, `q 3 C` and
   `r C B`. Note that `C` is an argument to both
   `q` and `r` and acts as a link: if solving `q`
   fixes `C` then the query for `r` sees that.
   Similarly for `B`, that is identified with X,
   and is hence a link from the solution of `r` to
   the solution of `p`.

   A clause like
     of (lam F) (arr A B) :-
       pi x\ of x A => of (F x) B.
   reads
     ∀F A B, (∀x, of x A => of (F x) B) => of (lam F) B.
   Hence, `x` and `of x A` are available only
   temporarily to prove  `of (F x) B` and this is
   also why `A` cannot change during such proof (A is
   quantified once and forall outside).

   Each program execution is a proof of the query
   and is made of the program clauses seen as axioms.

*)

(* ------------------------------------------------ *)

(* Wrap up

   The simple interpreter and type checker for
   the lambda calculus shows how easy it is to
   manipulate syntax trees with binders in λProlog.

   This piece of software (coq-elpi) embeds in Coq
   the elpi λProlog interpreter and exposes the
   Coq datatype of terms to such scripting language.
   See the header of "coq-lib.elpi".

   In addition to that it exposes to the scripting
   language a few basic API to query the environment
   of data types and constants as well as to add to
   such environment terms built by a λProlog program.

 *)

Elpi Run "
  coq-say ""That's all folks!""
".
