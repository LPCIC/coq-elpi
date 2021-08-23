(*|

Tutorial on the Elpi programming language
*****************************************

:author: Enrico Tassi

.. include:: tutorial_style.rst

..
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
   exposing to the extension language Coq specific data types (e.g. terms)
   and API (e.g. to declare a new inductive type).

   In order to get proper syntax highlighting using VSCode please install the
   "gares.coq-elpi-lang" extension. In CoqIDE please chose "coq-elpi" in
   Edit -> Preferences -> Colors.

This little tutorial does not talk about Coq, but rather focuses on
Elpi as a programming language. It assumes no previous knowledge of
Prolog and λProlog. Coq can be used as an environment for stepping trough
the tutorial one paragraph at a time. The text between `lp:{{` and `}}` is
Elpi code, while the rest are Coq directives to drive the interpreter.

.. contents::

|*)

From elpi Require Import elpi.

(*|

===============================================
Logic programming: unification and backtracking
===============================================

We start by introducing the first order fragment of
λProlog, i.e. the terms will not contain binders.

Our first program is called `tutorial`.

We begin by declaring the signature of our terms.
Here we declare that :elpi:`person` is a type, and that
:elpi:`mallory`, :elpi:`bob` and :elpi:`alice` are terms of that type.

|*)

Elpi Program tutorial lp:{{

  kind person  type.
  type mallory, bob, alice  person.

}}.

(*|

A λProlog program is made of clauses that declare
when a predicate holds and that are accumulated one after the
other.

The next commands accumulates on top
of the current `tutorial` program a predicate declaration for :elpi:`age`
and 3 clauses representing our knowledge about our terms.

Note that :stdtype:`int` is the primitive data type of integers.

|*)

Elpi Accumulate lp:{{

  pred age o:person, o:int.

  age mallory 23.
  age bob 23.
  age alice 20.

}}.

(*|

The predicate :elpi:`age` has two arguments, the former is a person while
the latter is an integer. The label :elpi:`o:` (standing for "output")
is a mode declaration. Modes will be explained later on, for now they can be
ignored.

Now we can run our program!  The entry point of a program is called a query,
i.e. a predicate expression containing variables such as

.. code:: elpi

     age alice A

The execution of the program is expected to assign to :elpi:`A` the
age of :elpi:`alice`.

.. important:: Syntactic conventions:

   * Variables are identifiers starting with a capital letter, eg
     :elpi:`A`, :elpi:`B`, :elpi:`FooBar`, :elpi:`Foo_bar`, :elpi:`X1`
   * constants (for individuals or predicates) are identifiers
     starting with a lowercase letter, eg
     :elpi:`foo`, :elpi:`bar`, :elpi:`this_that`, :elpi:`camelCase`,
     :elpi:`dash-allowed`, :elpi:`qmark_too?`, :elpi:`arrows->as_well`

A query can be composed of many predicate expressions linked by ``,``
that stands for conjunction: we want to get an answer to all of the
predicate expressions.

`coq.say` is a built-in predicate provided by Coq-Elpi: an API which
takes any arguments and makes Coq print them.

|*)

Elpi Query lp:{{

  age alice A, coq.say "The age of alice is" A

}}.

(*|
   
You can look at the output buffer of Coq to see the value for :elpi:`A` or hover
or toggle the little bubble after `}}.` if you are reading the tutorial with a
web browser.

Note that :stdtype:`string` is also a primitive data type; strings are delimited
by double quotes.

The predicate :elpi:`age` represents a relation (in contrast to a function) since it
computes both ways: we can ask Elpi which person :elpi:`P` is 23 years old.

|*)

Elpi Query lp:{{

  age P 23, coq.say P "is 23 years old"

}}.

(*|

Operationally the query :elpi:`age P 23` is *unified* with each
and every clause present in the program starting from the first one.

Unification compares two
terms structurally and eventually assigns variables.
For example for the first clause of the program we obtain
the following unification problem:

.. code:: elpi

     age P 23 = age mallory 23

This problem can be simplified into smaller unification problems following
the structure of the terms:

.. code:: elpi

     age = age
     P = mallory
     23 = 23

The first and last are trivial, while the second one can be satisfied by
assigning :elpi:`mallory` to :elpi:`P`. All equations are solved,
hence unification succeeds.

See also the `Wikipedia page on Unification <https://en.wikipedia.org/wiki/Unification_(computer_science)#Syntactic_unification_of_first-order_terms>`_.

The first part of the query is succesful and the rest of
the query is run: the value of :elpi:`P` is printed as well as
the :elpi:`"is 23 years old"` string.

Note that the :elpi:`=` sign is a regular predicate. Indeed the query
:elpi:`age P 23` can be rewritten as

.. code:: elpi

   A = 23, age P A, coq.say P "is 23 years old"


Let's try a query harder to solve!

|*)

Elpi Query lp:{{

  age P 20, coq.say P "is 20 years old"

}}.

(*|

This time the unification problem for the first clause
in the program is:

.. code:: elpi

     age P 20 = age mallory 23

that is simplified into:

.. code:: elpi

     age = age
     P = mallory
     20 = 23

The second equation assigns :elpi:`P`, but the third one fails.

When failure occurs, the next clause in the program is
tried and all assignements are undone, i.e. :elpi:`P` is fresh again.
This operation is called backtracking.

The unification problem for the next clause is:

.. code:: elpi

   age P 20 = age bob 23

This one also fails.  The last one is:

.. code:: elpi

   age P 20 = age alice 20

This one works, and the assigment :elpi:`P = alice` is kept as the result
of the first part of the query.

An even harder query is the following one where we ask for two distinct
individuals to have the same age.

|*)

Elpi Query lp:{{

  age P A, age Q A, not(P = Q),
  coq.say P "and" Q "are" A "years old"

}}.

(*|
   
This example shows that backtracking is global.  The first solution for
:elpi:`age P A` and :elpi:`age Q A` picks :elpi:`P` and :elpi:`Q` to
be the same individual :elpi:`mallory`,
but then :elpi:`not(P = Q)` fails and forces the last choice that was made to be
reconsidered, so :elpi:`Q` becomes :elpi:`bob`.

Look at the output of the following instrumented code:

|*)

Elpi Query lp:{{

   age P A, age Q A, coq.say "I picked" P "and" Q,
   not(P = Q),
   coq.say "the last choice worked!",
   coq.say P "and" Q "are" A "years old"

}}.

(*|
   
The clauses we have seen so far are facts: they always hold.
In general clauses can have premises: conditions necessary in
order to make the predicate hold.

Here we add to our program a clase that defines what :elpi:`older P Q` means
in terms of the :elpi:`age` of :elpi:`P` and :elpi:`Q`.
Note that :elpi:`>` is a built-in predicate
on numbers with the expected meaning.

|*)

Elpi Accumulate lp:{{

  pred older o:person, o:person.
  older P Q :- age P N, age Q M, N > M.

}}.

(*| Let's run a query using older |*)

Elpi Query lp:{{

  older bob X,
  coq.say "bob is older than" X

}}.

(*|

The query :elpi:`older bob X` is unified with the head of
the program clause :elpi:`older P Q` (what is to the left of :elpi:`:-`),
assigning :elpi:`P = bob` and :elpi:`X = Q`.  Then new queries are run:

.. code:: elpi

     age bob N
     age Q M
     N > M

The former assigns :elpi:`N = 23`, the second one first
sets :elpi:`Q = mallory` and :elpi:`M = 23`.  This makes the last
query to fail, since :elpi:`23 > 23` is false.  Hence the
second query is run again and again until :elpi:`Q` is
set to :elpi:`alice` and :elpi:`M` to :elpi:`20`.

Variables in the query are said to be existentially
quantified because λProlog will try to find one
possible value for them.

Conversely, the variables used in clauses are
universally quantified in the front of the clause.
This means that the same program clause can be used
multiple times, and each time the variables are fresh.

In the following example the variable :elpi:`P` in :elpi:`older P Q :- ...`
once takes :elpi:`bob` and another time takes :elpi:`mallory`.

|*)

Elpi Query lp:{{

  older bob X, older mallory X,
  coq.say "both bob and mallory are older than" X

}}.

(*|

=====================
Higher order features
=====================


So far the syntax of terms is based on constants
(eg :elpi:`age` or :elpi:`mallory`) and variables (eg :elpi:`X`).

λProlog adds to constants another term constructor:
λ-abstraction (written :elpi:`x\ ...`). The variable name
before the ``\`` can be capital as well: given that it is
explicitly bound Elpi needs not to guess if it is a global
symbol or a clause variable (that required the convention of
using capitals for variables).

Functions built using λ-abstraction can be applied
to arguments and honor the usual β-reduction rule
(the argument is substituted for the bound variable).

In the following example :elpi:`F 23` reads, once
the β-reduction is performed, :elpi:`age alice 23`.

|*)

Elpi Query lp:{{

  F = (x\ age alice x),
  coq.say "F =" F,
  coq.say "F 20 =" (F 20),
  coq.say "F 23 =" (F 23)

}}.

(*|

Let's now write the "hello world" of λProlog: an
interpreter and type checker for the simply
typed λ-calculus. We call this program `stlc`.

We start by declaring that :elpi:`term` is a type and
that :elpi:`app` and :elpi:`fun` are constructors of that type.

|*)

Elpi Program stlc lp:{{

  kind  term  type.

  type  app   term -> term -> term.
  type  fun   (term -> term) -> term.

}}.

(*|

The constructor :elpi:`app` takes two terms
while :elpi:`fun` only one (of functional type).

Note that

* there is no constructor for variables, we will
  use the notion of bound variable of λProlog in order
  to represent variables
* :elpi:`fun` takes a function as subterm, i.e. something
  we can build using the λ-abstraction :elpi:`x\ ...`

As a consequence, the identity function is written like this:

.. code:: elpi

   fun (x\ x)

while the :elpi:`first` function is written:

.. code:: elpi

   fun (x\ fun (y\ x))

Another consequence of this approach is that there is no
such thing as a free variable. One can have (global) constants,
but variables are only available under the λ-abstraction of the
programming language, that gives them a well defined scope and
substitution operation (β-reduction).

This approach is called `HOAS <https://en.wikipedia.org/wiki/Higher-order_abstract_syntax>`_.

We can now implement weak head reduction, that is we stop reducing
when the term is a :elpi:`fun` or a global constant (potentially applied).

If the term is :elpi:`app (fun F) A` then we compute the reduct elpi:`F A`.
Note that :elpi:`F` is a λProlog function, so passing an argument to it
implements the substitution of the actual argument for the bound variable.

We first give a type and a mode for our predicate :elpi:`whd`. It reads
"whd takes a term in input and gives a term in output". We will
explain what input means precisely later, for now just think about it
as a comment.

|*)

Elpi Accumulate lp:{{

  pred whd i:term, o:term.

  % when the head "Hd" of an "app" (lication) is a
  % "fun" we substitute and continue
  whd (app Hd Arg) Reduct :- whd Hd (fun F), !,
    whd (F Arg) Reduct.

  % otherwise a term X is already in normal form.
  whd X Reduct :- Reduct = X.

}}.

(*|

Recall that, due to backtracking, all clauses are potentially used.

Here, whenever the first premise of the first clause applies,
we want the second clause to be skipped, since we found a redex (that is not
in weak head normal form).

The premises of a clause are run in order, and the :elpi:`!` operator discards all
alternative clauses following the current one. Said otherwise it commits to
the currently chosen clause for the current query (but leaves
all clauses available for subsequent queries).

|*)

Elpi Query lp:{{

  I = (fun x\x),
  whd I T, coq.say "λx.x ~>" T,
  whd (app I I) T1, coq.say "(λx.x) (λx.x) ~>" T1

}}.

(*|

Another little test using global constants:

|*)
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

(*|

A last test with a lambda term that has no weak head normal form:

|*)

Elpi Bound Steps 1000. (* Let's be cautious *)
Fail Elpi Query lp:{{

  Delta = fun (x\ app x x),
  Omega = app Delta Delta,
  whd Omega Hummm, coq.say "not going to happen"

}}.
Elpi Bound Steps 0.

(*|

Remark we have used the binders of λProlog to implement substitution.
This feature is complemented by the :elpi:`pi` quatifier and the :elpi:`=>` connective
in order to be able to recurse under a binder.

A good showcase for these features is to implement a type checker
for the simply typed lambda calculus.
See also `the Wikipedia page on the simply typed lambda calculus <https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus>`_.

We start by defining the data type of simple types.
We then declare a new predicate :elpi:`of` (for "type of") and finally
we provide two clauses, one for each term constructor.

|*)

Elpi Accumulate lp:{{

  kind  ty   type.           % the data type of types
  type  arr  ty -> ty -> ty. % our type constructor

  pred of i:term, o:ty. % the type checking algorithm

  % for the app node we ensure the head is a function from
  % A to B, and that the argument is of type A
  of (app Hd Arg) B :-
    of Hd (arr A B), of Arg A.

  % for lambda, instead of using a context (a list) of bound
  % variables we use pi and => , explained below
  of (fun F) (arr A B) :-
    pi x\ of x A => of (F x) B.

}}.

(*|

The :elpi:`pi name\ code` syntax is reserved, as well as
:elpi:`clause => code`.

Operationally :elpi:`pi x\ code` introduces a fresh
constant :elpi:`c` for :elpi:`x` and then runs :elpi:`code`.
Operationally :elpi:`clause => code` adds :elpi:`clause` to
the program and runs :elpi:`code`.  Such extra clause is
said to be hypothetical.
Both the constant for :elpi:`x` and :elpi:`clause` are
removed once :elpi:`code` terminates.

.. important:: hypothetical clauses are added at the *top* of the program

   Hypothetical clauses hence take precedence over static clauses, since
   they are tried first.

Note that in this last example the hypothetical clause is going to be
:elpi:`of c A` for a fixed :elpi:`A` and a fresh constant :elpi:`c`.
The variable :elpi:`A` is fixed but not assigned yet, meaning
that :elpi:`c` has a type, and only one, but we may not know it yet.


Now let's assign a type to λx.λy.x:

|*)

Elpi Query lp:{{

of (fun (x\ fun y\ x)) Ty, coq.say "The type of λx.λy.x is:" Ty

}}.

(*|

Let's run this example step by step:

The clause for :elpi:`fun` is used:

* :elpi:`arrow A1 B1` is assigned to :elpi:`Ty` by unification
* the :elpi:`pi x\ ` quantifier creates a fresh constant :elpi:`c1` to play
  the role of :elpi:`x`
* the :elpi:`=>` connective adds the clause :elpi:`of c1 A1` the program
* the new query :elpi:`of (fun y\ c1) B1` is run.

Again, the clause for :elpi:`fun` is used (since its variables are
universally quantified, we use :elpi:`A2`, :elpi:`B2`... this time):

* :elpi:`arrow A2 B2` is assigned to :elpi:`B1` by unification
* the :elpi:`pi x\ ` quantifier creates a fresh constant :elpi:`c2` to play
  the role of :elpi:`x`
* the :elpi:`=>` connective adds the clause :elpi:`of c2 A2` the program
* the new query :elpi:`of c1 B2` is run.

The (hypotetical) clause :elpi:`of c1 A1` is used:

* unification assigns :elpi:`A1` to :elpi:`B2`

The value of :elpi:`Ty` is hence :elpi:`arr A1 (arr A2 A1)`, a good type
for λx.λy.x (the first argument and the output have the same type :elpi:`A1`).

What about the term λx.(x x) ?

|*)

Elpi Query lp:{{

  Delta = fun (x\ app x x),
  (of Delta Ty ; coq.say "Error:" Delta "has no type")

}}.

(*|
  
The :elpi:`;` infix operator stands for disjunction. Since we see the message
:elpi:`of` failed: the term :elpi:`fun (x\ app x x)` is not well typed.

First, the clause for elpi:`fun` is selected:

* :elpi:`arrow A1 B1` is assigned to :elpi:`Ty` by unification
* the :elpi:`pi x\ ` quantifier creates a fresh constant :elpi:`c1` to play the
  role of :elpi:`x`
* the :elpi:`=>` connective adds the clause :elpi:`of c1 A1` the program
* the new query :elpi:`of (app c1 c1) B1` is run.

Then it's the turn of typing the application:

* the query :elpi:`of c1 (arr A2 B2)` assignes to :elpi:`A1` the
  value :elpi:`arr A2 B2`.  This means that the
  hypothetical clause is now :elpi:`of c1 (arr A2 B2)`.
* the query :elpi:`of c1 A2` fails because the unification

  .. code:: elpi

     of c1 A2 = of c1 (arr A2 B2)

  has no solution, in particular the sub problem :elpi:`A2 = (arr A2 B2)`
  fails the so called occur check.


The semantics of a λProlog program is given by interpreting
it in terms of logical formulas and proof search.

A clause

.. code:: elpi

     p A B :- q A C, r C B.

has to be understood as a formula

.. math::

     ∀A~B~C, (\mathrm{q}~A~C ∧ \mathrm{r}~C~B) → \mathrm{p}~A~B

A query is a goal that is proved by backchaining
clauses.  For example :elpi:`p 3 X`
is solved by unifying it with the conclusion of
the formula above (that sets :elpi:`A` to :elpi:`3`) and
generating two new goals, :elpi:`q 3 C` and
:elpi:`r C B`. Note that :elpi:`C` is an argument to both
:elpi:`q` and :elpi:`r` and acts as a link: if solving :elpi:`q`
fixes :elpi:`C` then the query for :elpi:`r` sees that.
Similarly for :elpi:`B`, that is identified with :elpi:`X`,
and is hence a link from the solution of :elpi:`r` to
the solution of :elpi:`p`.

A clause like

.. code:: elpi

     of (fun F) (arr A B) :-
       pi x\ of x A => of (F x) B.

reads, as a logical formula:

.. math::

     ∀F~A~B, (∀x, \mathrm{of}~x~A → \mathrm{of}~(F~x)~B) → \mathrm{of}~(\mathrm{fun}~F)~(\mathrm{arr}~A~B)

or using the inference rule notation typically used for type systems

.. math::

      \frac{\Gamma, \mathrm{of}~x~A \vdash \mathrm{of}~(F~x)~B  \quad   x~\mathrm{fresh}}{\Gamma \vdash \mathrm{of}~(\mathrm{fun}~F)~(\mathrm{arr}~A~B)}

Hence, :elpi:`x` and :elpi:`of x A` are available only
temporarily to prove  :elpi:`of (F x) B` and this is
also why :elpi:`A` cannot change during this sub proof (:elpi:`A` is
quantified once and forall outside).

Each program execution is a proof of the query
and is made of the program clauses seen as axioms.

=====================
Modes and constraints
=====================

Elpi extends λProlog with syntactic constraints
and rules to manipulate the set of constraints.

Syntactic constraints are goals suspended on
a variable and are resumed as soon as such a variable
gets instantiated.

A companion facility is the declaration of modes.
The argument of a predicate can be marked as input
to avoid it being instantiated when unifying the
the goal with the head of a clause.

A simple example: Peano's addition

|*)

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

(*|
   
Unfortunately the relation does not work well
when the first argument is a variable.  Depending on the
order of the clauses for :elpi:`add` Elpi can either diverge or pick
:elpi:`z` as a value for :elpi:`X` (that may not be what one wants)

|*)

Elpi Bound Steps 100.
Fail Elpi Query lp:{{ add X (s z) Y }}.
Elpi Bound Steps 0.

(*|

Indeed the first clause for add can be applied forever.
If one exchanges the two clauses in the program, then Elpi
terminates picking :elpi:`z` for :elpi:`X`.

We can use the mode directive in order to
*match* arguments marked as i against the patterns
in the head of clauses, rather than unifying them.

|*)

Elpi Program peano2 lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred sum i:nat, i:nat, o:nat.

sum (s X) Y (s Z) :- sum X Y Z.
sum z X X.

}}.

Fail Elpi Query lp:{{ sum X (s z) Y }}.

(*|

The query fails because no clause first argument matches :elpi:`X`.

Instead of failing we can suspend goals and turn them into
syntactic constraints

|*)

Elpi Accumulate lp:{{

sum X Y Z :-
  % this clause always applies, we double check X is a variable
  var X,
  % then we declare the constraint and trigger its resumption of the
  % assignment of X
  declare_constraint (sum X Y Z) [X].

}}.

Elpi Query lp:{{ sum X (s z) Z }}.

(*|

Syntactic constraints are resumed when the variable
they are suspended on is assigned 

|*)

Elpi Query lp:{{

  sum X (s z) Z, X = z,
  coq.say "The result is:" Z,
  print_constraints % to be sure, prints nothing

}}.

(*|
  
A couple more examples:

* resumption can cause failure
* recall that :elpi:`;` stands for disjunction

|*)

Fail Elpi Query lp:{{ sum X (s z) (s (s z)), X = z }}.
Elpi Query lp:{{ sum X (s z) (s (s z)), (X = z ; X = s z) }}.

(*|

Remark how computation suspends, then makes progess,
then suspends again... 

|*)

Elpi Query lp:{{

   sum X (s z) Y,
   print_constraints, coq.say "Currently Y =" Y,
   X = s Z,
   print_constraints, coq.say "Currently Y =" Y,
   Z = z,
   coq.say "Finally Y =" Y

}}.

(*|

Sometimes the set of syntactic constraints becomes unsatisfiable
and we would like to be able to fail early. 

|*)

Elpi Accumulate lp:{{

pred even i:nat.
pred odd  i:nat.

even z.
even (s X) :- odd X.
odd (s X) :- even X.

odd X :- var X, declare_constraint (odd X) [X].
even X :- var X, declare_constraint (even X) [X].

}}.

Elpi Query lp:{{ even (s X), odd (s X) }}.

(*|

A constraint (handling) rule can see the set of syntactic constraints
as a whole, remove constraints and/or create new goals

|*)

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

(*|

.. note:: :elpi:`fail` is a predicate with no solution

See also the Wikipedia page on `Constraint Handling Rules <https://en.wikipedia.org/wiki/Constraint_Handling_Rules>`_
for an introduction to the sub language to manipualte constraints.

================
Functional style
================

Elpi is a relational language, not a functional one. Still some features
typical of functional programming are available, with some caveats.

First, functions about built-in data types are available via the infix :elpi:`is`
predicate

|*)

Elpi Query lp:{{  X is 3 + 2, Y is "result " ^ "=", coq.say Y X }}.

(*|

Chaining "relations" can be painful, especially when
they look like functions. Here we use :stdlib:`std.append`
and :stdlib:`std.rev` as examples.

|*)

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
  % - [ E1, E2 | Tail ] for iterated cons, where
  %     | Tail can be omitted if the list is nil terminated
  make-palindrome [1,2,3] A,
  make-palindrome2 [1,2,3] B,
  coq.say A "=" B

}}.

(*|

The two programs are equivalent, and indeed the latter is
elaborated into the former. Expressions between `{` and `}` are
said to be spilled out and placed just before the predicate
that contains them.

The :stdlib:`calc` predicate is just a wrapper around the infix :elpi:`is`

|*)

Elpi Query lp:{{ coq.say "result =" {calc (2 + 3)} }}.

(*|
   
Higher order predicates can be defined, but one has to be wary
of where variables are bound.

|*)

Elpi Accumulate lp:{{

pred bad i:list int, o:list int.

% Note that the standard library declares
%   pred std.map i:list A, i:(A -> B -> prop), o:list B.
% Remark "prop" is the type of predicates and that the type
% of "std.map" declared by the "pred" directive is
%   type std.map list A -> (A -> B -> prop) -> list B -> prop
% Indeed "pred" extends a type declaration (for predicates,
% hence the trailing -> prop is implicit) with a mode
% declaration for each argument.
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

(*|

The problem with :elpi:`bad` is that :elpi:`TMP` is fresh each time the clause
is used, but not every time the anonymous predicate passed to :stdlib:`map`
is used. Technically :elpi:`TMP` is quantified (allocated) where :elpi:`L`
and :elpi:`Result` are.

There are two ways to quantify :elpi:`TMP` correctly, that is inside the
anonymous predicate. One is to actually name the predicate. Another one is
to use the :elpi:`sigma x\ ` quantifier to allocate :elpi:`TMP` at every call.

One last way to skin the cat is to use :elpi:`=>` as follows. It gives us
the occasion to clarify further the scope of variables. 

|*)

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

(*|

In this case the auxiliary predicate :elpi:`good3.aux`
is only visible inside :elpi:`good3`.
What is interesting to remark is that the quantifications are explicit
in the hypothetical clause, and they indicate clearly that each and every
time :elpi:`good3.aux` is used :elpi:`TMP`, :elpi:`X` and :elpi:`R` are fresh.

The :elpi:`pi x\ ` quantifier is dual to :elpi:`sigma x\ `: since here it
occurs negatively it has the same meaning.

The last remark worth making is that bound variables are intimately related
to universal quantification, while unification variables are related to
existential quantification.  It goes without saying that the following
two queries are not equivalent and while the former is trivial the latter
is false:

.. math::

     ∀x, ∃Y, Y = x\\
     ∃Y, ∀x, Y = x

Let's run these queries:

|*)

Elpi Query lp:{{ pi x\ sigma Y\ Y = x }}.
Fail Elpi Query lp:{{ sigma Y\ pi x\ Y = x }}.

(*|

Another way to put it: :elpi:`x` is in the scope of :elpi:`Y` only in the first formula,
hence :elpi:`x` can be assigned to :elpi:`Y` in that case only.

More in general, λProlog tracks the bound variables that are in scope of each
unification variable. There are only two ways to put a bound variable
in the scope:

* quantify the unification variable under the bound one (first formula)
* pass the bound variable to the unification variable explicitly: in this
  the case the unification variable needs to have a functional type.
  Indeed :math:`∃Y, ∀x, (Y x) = x` has a solution: :elpi:`Y` can be the identity function.

If we look again at the clause for type checking
lambda abstraction

.. code:: elpi

     of (fun F) (arr A B) :-
       pi x\ of x A => of (F x) B.

we can read the scopes (recall all unification variables such as :elpi:`F`, :elpi:`A`, :elpi:`B` are
quantified upfront). The only unification variable that sees the fresh
`x` is :elpi:`F`, because we pass :elpi:`x` to :elpi:`F` explicitly. Indeed when we write

.. math::

    \frac{\Gamma, x : A \vdash f : B}{\Gamma \vdash λx.f : A → B}

on paper, the :elpi:`x` being bound can only occur in f (not in `𝚪` or `B` for example).
Remark that in the premise x is still bound, this time not by a λ but by the
context `𝚪, x : A`. In λProlog the context is the set of hypothetical clauses
and pi-quantified variables and is implicitly handled by the runtime of the
programming language.

A slogan to keep in mind is that:

.. important::  There is not such as thing as a free variable!

and indeed the variable bound by the lambda abstraction (of our data) is
replaced by a fresh variable bound by the context (of our program). This is
called binder mobility. See also the paper 
`Mechanized metatheory revisited <https://hal.inria.fr/hal-01884210/>`_ by
Dale Miller which is an excellent
introduction to these concepts.

=========
Debugging
=========

A common λProlog idiom is to have a debug clause
lying around.  The :elpi:`:if` attribute can be used to
make the clause conditionally interpreted (only if the
given debug variable is set).

|*)

Elpi Debug "DEBUG_MYPRED".
Elpi Program debug lp:{{

  pred mypred i:int.

  :if "DEBUG_MYPRED"
  mypred X :-
    coq.say "calling mypred on " X, fail.

  mypred 0 :- coq.say "ok".
  mypred M :- N is M - 1, mypred N.

}}.
Elpi Query lp:{{ mypred 3 }}.

(*|
   
As a slightly more sophisticated debugging feature, the Elpi interpreter
provides tracing facilities. 

|*)

Elpi Trace.

Elpi Query stlc lp:{{ % We run the query in the stlc program

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

Fail Elpi Query stlc lp:{{

  of (fun (x\ app x x)) Ty, coq.say Ty

}}.

(*|

The trace can be limited to a range of steps. Look at the
numbers ``run HERE {{{``. 
   
|*)

Elpi Trace 6 8.
Elpi Query stlc lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

(*|
   
The trace can be limited to a (list of) predicates as follows:

|*)

Elpi Trace "of".
Elpi Query stlc lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

(*|

One can combine the range of steps with the predicate:

|*)

Elpi Trace 6 8 "of".
Elpi Query stlc lp:{{

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

(*|

To switch traces off:

|*)

Elpi Trace Off.

(*|
   
Given that programs are not written in a single place, but rather obtained by
accumulating code, Elpi is able to print a (full) program to an html file
as follows. The obtained file provides a facility to filter clauses by their
predicate. 

|*)

Elpi Print stlc "stlc.html".

(*|

Look at the `generated page <https://lpcic.github.io/coq-elpi/stlc.html>`_
and type :elpi:`of` in the filter.

Finally, one can bound the number of backchaining steps
performed by the interpreter:

|*)

Elpi Query lp:{{ 0 = 0, 1 = 1 }}.
Elpi Bound Steps 1.
Fail Elpi Query lp:{{ 0 = 0, 1 = 1 }}. (* it needs more than 1 step! *)
Elpi Bound Steps 0. (* Go back to no bound *)

(*|

===============
Further reading
===============

The `λProlog website <http://www.lix.polytechnique.fr/~dale/lProlog/>`_
contains useful links to λProlog related material.

Papers and other documentation about Elpi can be found at
the `Elpi home on github <https://github.com/LPCIC/elpi/>`_.

Three more tutorials specific to Elpi as an extension language for Coq
can be found in the `examples folder <https://github.com/LPCIC/coq-elpi/blob/master/examples/>`_.
You can continue by reading the one about the 
`HOAS for Coq terms <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html>`_.

|*)


