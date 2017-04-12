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

fix sum {struct 1} forall _ : Tree, nat :=
  fun (t : Tree) =>
    match t in Tree return nat with
    | Leaf =>
        fun (n : nat) => n
    | Node =>
        fun (l : Tree) =>
        fun (r : Tree) =>
          Nat.add (sum l) (sum r)
  end

*)

(* The bare bones terms are built from
   - constants (Nat.add, Leaf, Tree, nat)
   - pattern matching
   - fixpoints (recursive functions)
   - lambda abstraction (fun)
   - function application (juxtaposition)

   Plus the following ones, not visible in this example
   - sorts (Type, Prop)
   - let-in (local definition)
   - type casts (typing annotations) *)

(* ------------------------------------------------ *)
(* Boilerplate, please ignore *)
From elpi Require Import elpi.
Elpi Init "./" "../elpi/".
Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate "
type $$$coq-say A -> B.
coq-say A :- $coq-say A.
".
(* End Boilerplate *)

(* Elpi is an embedded λProlog interpreter.
   λProlog is a programming language designed to
   manipulate syntax trees containing binders.
   A λProlog is made of clauses that declare when
   a delation holds. *)

(* In CoqIDE please chose "coq-elpi" in
     Edit -> Preferences -> Colors
   to have proper syntax highlight.*)

Elpi Accumulate "
 % 3 clauses about the relation `age`
 age mallory 23.
 age bob 23.
 age alice 20.
 % a clause about the relation `friend`
 friend bob alice.
 % a clause about `older` with 3 premises. The meaning
 % is that `older` holds when all premises hold.
 older P Q :- age P N, age Q M, N > M.
".
(* age is a relation, it `computes` both ways:
   the query is unified with all clauses, variables
   (written in capitals) are assigned *)
Elpi Run "
  age alice A, coq-say ""Alice is "", coq-say A.
".
Elpi Run "
  age P 23, coq-say P, coq-say "" is 23"".
".
Fail Elpi Run "age bob A, age alice A.".

(* bob is older than... who? *)
Elpi Run "older bob P, coq-say P.".

(* The computation is based on backtracking, e.g.
   `age P 23` has two solutions for P, but only
   one works for the `friend` relation.
   Note that clauses are tried in order, so P is
   first mallory, then bob. *)

Elpi Run "age P 23,
          coq-say ""attempt "", coq-say P,
          friend P alice,
          coq-say ""finally"", coq-say P".

(* A query as `age P 20` is unified with each
   and every clause. For example for the first
   clause we obtain
     `age P 20 = age mallory 23`
   that is simplified into smaller equations
     `age = age`
     `P = mallory`
     `23 = 20`
   the second can be satisfied by assigning mallory to P
   the third one fail, so the next clause is tried and
   all assignments are backtracked
     `age P 20 = age bob 23`
   this one also fails.  the last one
     `age P 20 = age alice 20`
   works and the assigment P = alice is kept

   See also: https://en.wikipedia.org/wiki/Unification_(computer_science)#Syntactic_unification_of_first-order_terms
*)

(* TODO: variables are quantified in front of the clause,
 at each use they are fresh *)

(* So far the syntax of terms is based on constants
   (called functors, eg age or mallory) and variables
   (begin with a capital, eg X, Person, Result).

   λProlog adds to that lambda abstraction (written x\...)
   and beta-reduction
*)
Elpi Run "
  F = (x\ friend x alice),
  F bob, not(F mallory).
".

(* Let's write the hello world of λProlog, an interpreter
   and type checker for the simply typed lambda calculus *)

Elpi Accumulate "
% we give some type declarations, mainly a documentation
kind  term type. % `term` is a new type

% we give two term constructors: `app` and `lam`
type  app term -> term -> term.
type  lam (term -> term) -> term.
".

(* Note that:
   - there is no constructor for variables, we will 
     use the notion of bound variable of λProlog
   - `lam` takes a function as subterm

   The identity function is hence written
     lam (x\ x)
   While the `fst` function is written
     lam (x\ lam y\ x)

   This approach is called HOAS:
     https://en.wikipedia.org/wiki/Higher-order_abstract_syntax
*)

(* The interpreter *) 
Elpi Accumulate "
whd (app Hd Arg) Reduct :-
  whd Hd (lam F), whd (F Arg) Reduct.
whd X X.
".

(* little test *)
Elpi Run "
  Fst = lam (x\ lam y\ x),
  T = app (app Fst foo) bar,
  whd T T1, coq-say T1,
  S = app foo bar,
  whd S S1, coq-say S1.
".

(* better test... ;-) *)
Fail Timeout 1 Elpi Run "
  Delta = lam (x\ app x x),
  Omega = app Delta Delta,
  whd Omega Hummm, coq-say ""not going to happen"".
".

(* Let's rule out this nasty omega with a type system *)
Elpi Accumulate "
kind  ty type.
type  arr ty -> ty -> ty.

of (app Hd Arg) B :-
  of Hd (arr A B), of Arg A.
of (lam F) (arr A B) :-
  pi x\ of x A => of (F x) B.
".

(* `pi <name>\ <code>` is a reserved syntax, as well as
   `<code> => <code>.
   Operationally `pi x\ code` introduces a fresh
   constant x and then runs code.
   Operationally `clause => code` adds `clause` to 
   the program and runs code.  Such extra clause is
   said to be hypothetical.
   Both x and `clause` are removed once code terminates.

   Note that the hypothetical clause is `of x A` for
   a fixed A.
*)

Elpi Run "
  of (lam (x\ lam y\ x)) Ty, coq-say Ty.
".

(* Let's run step by step this example.

  The clause for lam is used:
  - Ty is assigned (arrow A1 B1)
  - a fresh c1 is created by the pi construct
  - `of c1 A1` is added to the program by the => construct,
  - the new query `of (lam y\ c1) B1` is run.
  Again, the clause for lam is used:
  - B1 is assigned (arrow A2 B2)
  - a fresh c2 is created by the pi construct
  - `of c2 A2` is added to the program by the => construct,
  - the new query `of c1 B2` is run.
  The (hypotetical) clause `of c1 A1` is used:
  - B2 gets assigned to A1

  The value of Ty is hence (arr A1 (arr A2 A1))

*)


Fail Elpi Run "
  Delta = lam (x\ app x x),
  of Delta Ty, coq-say Ty.
".

(* The term `lam (x\ app x x)` is not well typed:

  The clause for lam is used:
  - Ty is assigned (arrow A1 B1)
  - a fresh c1 is created by the pi construct
  - `of c1 A1` is added to the program by the => construct,
  - the new query `of (app c1 c1) B1` is run.
  The clause for app is used:
  - the query `of c1 (arr A2 B2)` assigned to A1 the
    value (arr A2 B2).  This means that the
    hypothetical clause is now `of c1 (arr A2 B2)`.
  - the query `of c1 A2` fails because
    `A2 = (arr A2 B2)` has no solution

*)

(* TODO: wrap up

   - the simple example shows how one can easily
     manipulate the syntax of lambda calculus in order
     to implement an interpreter and a type checker
     in elpi

   - coq-elpi embeds in coq the elpi interpreter and
     provides an HOAS encoding of Coq terms, see the
     header of `coq-lib.elpi`.
     coq-elpi also provides some basic APIs to
     access the Coq environment and to add to it
     new constants.

 *)
