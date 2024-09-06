(*|

Tutorial on the Elpi programming language
*****************************************

:author: Enrico Tassi

.. include:: ../etc/tutorial_style.rst

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
Prolog, λProlog or Elpi. Coq is used as an environment for stepping trough
the tutorial one paragraph at a time. The text between `lp:{{` and `}}` is
Elpi code, while the rest are Coq directives to drive the Elpi interpreter.

.. contents::

|*)

From elpi Require Import elpi. (* .none *)

(*|

=================
Logic programming
=================

Elpi is a dialect of λProlog enriched with constraints. We start by introducing
the first order fragment of λProlog, i.e. the terms will not contain binders.
Later we cover terms with binders and constraints.

Our first program is called `tutorial`.
We begin by declaring the signature of our terms.
Here we declare that :e:`person` is a type, and that
:e:`mallory`, :e:`bob` and :e:`alice` are terms of that type.

|*)

Elpi Program tutorial lp:{{

  kind person  type.
  type mallory, bob, alice  person.

}}.

(*|

An Elpi program is made of rules that declare
when predicates hold and that are accumulated one after the
other. Rules are also called clauses in Prolog's slang, so we may use both
terms interchangeably.

The next code snippet accumulates on top
of the current `tutorial` program a predicate declaration for :e:`age`
and three rules representing our knowledge about our terms.

|*)

Elpi Accumulate lp:{{

  pred age o:person, o:int.

  age mallory 23.
  age bob 23.
  age alice 20.

}}.

(*|

The predicate :e:`age` has two arguments, the former is a person while
the latter is an integer. The label :e:`o:` (standing for output)
is a mode declaration, which we will explain later (ignore it for now).

.. note:: :stdtype:`int` is the built-in data type of integers

   Integers come with usual arithmetic operators, see the :stdlib:`calc` built-in.

In order to run our program we have to write a query,
i.e. a predicate expression containing variables such as:

.. code:: elpi

   age alice A

The execution of the program is expected to assign a value to :e:`A`, which
represents the age of :e:`alice`.

.. important:: 

   Syntactic conventions:

   * variables are identifiers starting with a capital letter, eg
     :e:`A`, :e:`B`, :e:`FooBar`, :e:`Foo_bar`, :e:`X1`
   * constants (for individuals or predicates) are identifiers
     starting with a lowercase letter, eg
     :e:`foo`, :e:`bar`, :e:`this_that`, :e:`camelCase`,
     :e:`dash-allowed`, :e:`qmark_too?`, :e:`arrows->and.dots.as<-well`

A query can be composed of many predicate expressions separated by :e:`,`
that stands for conjunction: we want to get an answer to all the
predicate expressions.

|*)

Elpi Query lp:{{

  age alice A, coq.say "The age of alice is" A

}}.

(*|
   
:builtin:`coq.say` is a built-in predicate provided by Coq-Elpi which
prints its arguments.
You can look at the output buffer of Coq to see the value for :e:`A` or hover
or toggle the little bubble after `}}.` if you are reading the tutorial with a
web browser.

.. note:: :stdtype:`string` is a built-in data type

   Strings are delimited by double quotes and ``\`` is the escape symbol.

The predicate :e:`age` represents a *relation* (in contrast to a function)
and it computes both ways: we can ask Elpi which person :e:`P` is 23 years old.

|*)

Elpi Query lp:{{

  age P 23, coq.say P "is 23 years old"

}}.

(*|

-----------
Unification
-----------

Operationally the query :e:`age P 23` is *unified* with each
and every rule present in the program starting from the first one.

Unification compares two
terms structurally and eventually assigns variables.
For example for the first rule of the program we obtain
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
assigning :e:`mallory` to :e:`P`. All equations are solved,
hence unification succeeds.

See also the `Wikipedia page on Unification <https://en.wikipedia.org/wiki/Unification_(computer_science)#Syntactic_unification_of_first-order_terms>`_.

Since the first part of the query is successful the rest of
the query is run: the value of :e:`P` is printed as well as
the :e:`"is 23 years old"` string.

.. note:: :e:`=` is a regular predicate

   The query :e:`age P 23` can be also written as follows:

   .. code:: elpi
   
      A = 23, age P A, Msg = "is 23 years old", coq.say P Msg


Let's try a query harder to solve!

|*)

Elpi Query lp:{{

  age P 20, coq.say P "is 20 years old"

}}.

(*|

This time the unification problem for the first rule
in the program is:

.. code:: elpi

     age P 20 = age mallory 23

that is simplified to:

.. code:: elpi

     age = age
     P = mallory
     20 = 23

The second equation can be solved by assigning :e:`mallory` to :e:`P`,
but the third one has no solution, so unification fails.

------------
Backtracking
------------

When failure occurs all assignments are undone (i.e. :e:`P` is unset again)
and the next rule in the program is tried. This operation is called
*backtracking*.

The unification problem for the next rule is:

.. code:: elpi

   age P 20 = age bob 23

This one also fails. The unification problem for the last rule is:

.. code:: elpi

   age P 20 = age alice 20

This one works, and the assignment :e:`P = alice` is kept as the result
of the first part of the query. Then :e:`P` is printed and the program
ends.

An even harder query is the following one where we ask for two distinct
individuals to have the same age.

|*)

Elpi Query lp:{{

  age P A, age Q A, not(P = Q),
  coq.say P "and" Q "are" A "years old"

}}.

(*|
   
This example shows that backtracking is global.  The first solution for
:e:`age P A` and :e:`age Q A` picks :e:`P` and :e:`Q` to
be the same individual :e:`mallory`,
but then :e:`not(P = Q)` fails and forces the last choice that was made to be
reconsidered, so :e:`Q` becomes :e:`bob`.

Look at the output of the following code to better understand
how backtracking works.

|*)

Elpi Query lp:{{

   age P A, coq.say "I picked P =" P,
   age Q A, coq.say "I picked Q =" Q,
   not(P = Q),
   coq.say "the last choice worked!",
   coq.say P "and" Q "are" A "years old"

}}.

(*|
   
.. note:: :e:`not` is a black hole

   The :e:`not(P)` predicate tries to solve the query :e:`P`: it fails if
   :e:`P` succeeds, and succeeds if :e:`P` fails. In any case no trace is left
   of the computation for :e:`P`. E.g. :e:`not(X = 1, 2 < 1)` succeeds, but
   the assignment for :e:`X` is undone. See also the section
   about the `foundations`_ of λProlog.

---------------------------
Facts and conditional rules
---------------------------

The rules we have seen so far are *facts*: they always hold.
In general rules can only be applied if some *condition* holds. Conditions are
also called premises, we may use the two terms interchangeably.

Here we add to our program a rule that defines what :e:`older P Q` means
in terms of the :e:`age` of :e:`P` and :e:`Q`.

.. note:: :e:`:-` separates the *head* of a rule from the *premises*

|*)

Elpi Accumulate lp:{{

  pred older o:person, o:person.
  older P Q :- age P N, age Q M, N > M.

}}.

(*|

The rule reads: :e:`P` is older than :e:`Q` if
:e:`N` is the age of :e:`P`
*and* :e:`M` is the age of :e:`Q`
*and* :e:`N` is greater than :e:`M`.

Let's run a query using older:

|*)

Elpi Query lp:{{

  older bob X,
  coq.say "bob is older than" X

}}.

(*|

The query :e:`older bob X` is unified with the head of
the program rule :e:`older P Q`
assigning :e:`P = bob` and :e:`X = Q`.  Then three new queries are run:

.. code:: elpi

     age bob N
     age Q M
     N > M

The former assigns :e:`N = 23`, the second one first
sets :e:`Q = mallory` and :e:`M = 23`.  This makes the last
query to fail, since :e:`23 > 23` is false.  Hence the
second query is run again and again until :e:`Q` is
set to :e:`alice` and :e:`M` to :e:`20`.

Variables in the query are said to be existentially
quantified because Elpi will try to find one
possible value for them.

Conversely, the variables used in rules are
universally quantified in the front of the rule.
This means that the same program rule can be used
multiple times, and each time the variables are fresh.

In the following example the variable :e:`P` in :e:`older P Q :- ...`
once takes :e:`bob` and another time takes :e:`mallory`.

|*)

Elpi Query lp:{{

  older bob X, older mallory X,
  coq.say "both bob and mallory are older than" X

}}.

(*|

==================
Terms with binders
==================

So far the syntax of terms is based on constants
(eg :e:`age` or :e:`mallory`) and variables (eg :e:`X`).

λProlog adds another term constructor:
λ-abstraction (written :e:`x\ ...`). 

.. note:: the variable name before the ``\`` can be a capital

   Given that it is explicitly bound Elpi needs not to guess if it is a global
   symbol or a rule variable (that required the convention of using capitals for
   variables in the first place).

-------------
λ-abstraction
-------------

Functions built using λ-abstraction can be applied
to arguments and honor the usual β-reduction rule
(the argument is substituted for the bound variable).

In the following example :e:`F 23` reads, once
the β-reduction is performed, :e:`age alice 23`.

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

We start by declaring that :e:`term` is a type and
that :e:`app` and :e:`fun` are constructors of that type.

|*)

Elpi Program stlc lp:{{

  kind  term  type.

  type  app   term -> term -> term.
  type  fun   (term -> term) -> term.

}}.

(*|

The constructor :e:`app` takes two terms
while :e:`fun` only one (of functional type).

Note that

* there is no constructor for variables, we will
  use the notion of bound variable of λProlog in order
  to represent variables
* :e:`fun` takes a function as subterm, i.e. something
  we can build using the λ-abstraction :e:`x\ ...`

As a consequence, the identity function λx.x is written like this:

.. code:: elpi

   fun (x\ x)

while the first projection λx.λy.x is written:

.. code:: elpi

   fun (x\ fun (y\ x))

Another consequence of this approach is that there is no
such thing as a free variable in our representation of the λ-calculus.
Variables are only available under the λ-abstraction of the
programming language, that gives them a well defined scope and
substitution operation (β-reduction).

This approach is called `HOAS <https://en.wikipedia.org/wiki/Higher-order_abstract_syntax>`_.

We can now implement weak head reduction, that is we stop reducing
when the term is a :e:`fun` or a global constant (potentially applied).
If the term is :e:`app (fun F) A` then we compute the reduct :e:`F A`.
Note that :e:`F` is a λProlog function, so passing an argument to it
implements the substitution of the actual argument for the bound variable.

We first give a type and a mode for our predicate :e:`whd`. It reads
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

Recall that, due to backtracking, all rules are potentially used.
Here whenever the first premise of the first rule succeeds
we want the second rule to be skipped, since we found a redex.

The premises of a rule are run in order and the :e:`!` operator discards all
other rules following the current one. Said otherwise it commits to
the currently chosen rule for the current query (but leaves
all rules available for subsequent queries, they are not erased from the
program). So, as soon as :e:`whd Hd (fun F)` succeeds we discard the second
rule.

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

}}.  (* .fails *)
Elpi Bound Steps 0.

(*|

-----------------------
:e:`pi x\ ` and :e:`=>`
-----------------------

We have seen how to implement substitution using the binders of λProlog.
More often than not we need to move under binders rather than remove them by
substituting some term in place of the bound variable. 

In order to move under a binder and inspect the body of a function λProlog
provides the :e:`pi` quantifier and the :e:`=>` connective.

A good showcase for these features is to implement a type checker
for the simply typed lambda calculus.
See also `the Wikipedia page on the simply typed lambda calculus <https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus>`_.

We start by defining the data type of simple types.
We then declare a new predicate :e:`of` (for "type of") and finally
we provide two rules, one for each term constructor.

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

The :e:`pi name\ code` syntax is reserved, as well as
:e:`rule => code`.

Operationally :e:`pi x\ code` introduces a fresh
constant :e:`c` for :e:`x` and then runs :e:`code`.
Operationally :e:`rule => code` adds :e:`rule` to
the program and runs :e:`code`.  Such extra rule is
said to be hypothetical.
Both the constant for :e:`x` and :e:`rule` are
removed once :e:`code` terminates.

.. important:: hypothetical rules are added at the *top* of the program

   Hypothetical rules hence take precedence over static rules, since
   they are tried first.

Note that in this last example the hypothetical rule is going to be
:e:`of c A` for a fixed :e:`A` and a fresh constant :e:`c`.
The variable :e:`A` is fixed but not assigned yet, meaning
that :e:`c` has a type, and only one, but we may not know it yet.


Now let's assign a type to λx.λy.x:

|*)

Elpi Query lp:{{

of (fun (x\ fun y\ x)) Ty, coq.say "The type of λx.λy.x is:" Ty

}}.

(*|

Let's run this example step by step:

The rule for :e:`fun` is used:

* :e:`arrow A1 B1` is assigned to :e:`Ty` by unification
* the :e:`pi x\ ` quantifier creates a fresh constant :e:`c1` to play
  the role of :e:`x`
* the :e:`=>` connective adds the rule :e:`of c1 A1` the program
* the new query :e:`of (fun y\ c1) B1` is run.

Again, the rule for :e:`fun` is used (since its variables are
universally quantified, we use :e:`A2`, :e:`B2`... this time):

* :e:`arrow A2 B2` is assigned to :e:`B1` by unification
* the :e:`pi x\ ` quantifier creates a fresh constant :e:`c2` to play
  the role of :e:`x`
* the :e:`=>` connective adds the rule :e:`of c2 A2` the program
* the new query :e:`of c1 B2` is run.

The (hypothetical) rule :e:`of c1 A1` is used:

* unification assigns :e:`A1` to :e:`B2`

The value of :e:`Ty` is hence :e:`arr A1 (arr A2 A1)`, a good type
for λx.λy.x (the first argument and the output have the same type :e:`A1`).

What about the term λx.(x x) ?

|*)

Elpi Query lp:{{

  Delta = fun (x\ app x x),
  (of Delta Ty ; coq.say "Error:" Delta "has no type")

}}.

(*|
  
The :e:`;` infix operator stands for disjunction. Since we see the message
:e:`of` failed: the term :e:`fun (x\ app x x)` is not well typed.

First, the rule for elpi:`fun` is selected:

* :e:`arrow A1 B1` is assigned to :e:`Ty` by unification
* the :e:`pi x\ ` quantifier creates a fresh constant :e:`c1` to play the
  role of :e:`x`
* the :e:`=>` connective adds the rule :e:`of c1 A1` the program
* the new query :e:`of (app c1 c1) B1` is run.

Then it's the turn of typing the application:

* the query :e:`of c1 (arr A2 B2)` assigns to :e:`A1` the
  value :e:`arr A2 B2`.  This means that the
  hypothetical rule is now :e:`of c1 (arr A2 B2)`.
* the query :e:`of c1 A2` fails because the unification

  .. code:: elpi

     of c1 A2 = of c1 (arr A2 B2)

  has no solution, in particular the sub problem :e:`A2 = (arr A2 B2)`
  fails the so called occur check.


.. _foundations:

===================
Logical foundations
===================

This section tries to link, informally, λProlog with logic, assuming the reader
has some familiarity with first order intuitionistic logic and proof theory.
The reader which is not familiar with that can probably skip this section,
although section `functional-style`_ contains some explanations about
the scope of variables which are based on the logical foundations of
the language.

The semantics of a λProlog program is given by interpreting
it in terms of logical formulas and proof search in intuitionistic logic.

A rule

.. code:: elpi

     p A B :- q A C, r C B.

has to be understood as a formula

.. math::

     ∀A~B~C, (\mathrm{q}~A~C ∧ \mathrm{r}~C~B) → \mathrm{p}~A~B

A query is a goal that is proved by backchaining
rules.  For example :e:`p 3 X`
is solved by unifying it with the conclusion of
the formula above (that sets :e:`A` to :e:`3`) and
generating two new goals, :e:`q 3 C` and
:e:`r C B`. Note that :e:`C` is an argument to both
:e:`q` and :e:`r` and acts as a link: if solving :e:`q`
fixes :e:`C` then the query for :e:`r` sees that.
Similarly for :e:`B`, that is identified with :e:`X`,
and is hence a link from the solution of :e:`r` to
the solution of :e:`p`.

A rule like:

.. code:: elpi

     of (fun F) (arr A B) :-
       pi x\ of x A => of (F x) B.

reads, as a logical formula:

.. math::

     ∀F~A~B, (∀x, \mathrm{of}~x~A → \mathrm{of}~(F~x)~B) → \mathrm{of}~(\mathrm{fun}~F)~(\mathrm{arr}~A~B)

where :math:`F` stands for a function.
Alternatively, using the inference rule notation typically used for
type systems:

.. math::

      \frac{\Gamma, \mathrm{of}~x~A \vdash \mathrm{of}~(F~x)~B  \quad   x~\mathrm{fresh}}{\Gamma \vdash \mathrm{of}~(\mathrm{fun}~F)~(\mathrm{arr}~A~B)}

Hence, :e:`x` and :e:`of x A` are available only
temporarily to prove  :e:`of (F x) B` and this is
also why :e:`A` cannot change during this sub proof (:e:`A` is
quantified once and forall outside).

Each program execution is a proof (tree) of the query
and is made of the program rules seen as proof rules or axioms.

As we hinted before negation is a black hole, indeed the usual definition of
:math:`\neg A` as :math:`A \to \bot` is the one of a function with no output
(see also the `the Wikipedia page on the Curry-Howard correspondence <https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence#Natural_deduction_and_lambda_calculus>`_).

=====================
Modes and constraints
=====================

Elpi extends λProlog with *syntactic constraints*
and rules to manipulate the store of constraints.

Syntactic constraints are goals suspended on
a variable which are resumed as soon as that variable
gets instantiated. While suspended they are kept in a store
which can be manipulated by dedicated rules.

A companion facility is the declaration of *modes*.
The argument of a predicate can be marked as input
to avoid instantiating the goal when it is unified
with the head of a rule (an input argument
is matched, rather than unified).

A simple example: Peano's addition:

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
order of the rules for :e:`add` Elpi can either diverge or pick
:e:`z` as a value for :e:`X` (that may not be what one wants)

|*)

Elpi Bound Steps 100.
Fail Elpi Query lp:{{ add X (s z) Y }}.  (* .fails *)
Elpi Bound Steps 0.

(*|

Indeed the first rule for add can be applied forever.
If one exchanges the two rules in the program, then Elpi
terminates picking :e:`z` for :e:`X`.

We can use the mode directive in order to
*match* arguments marked as :e:`i:` against the patterns
in the head of rules, rather than unifying them.

|*)

Elpi Program peano2 lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred sum i:nat, i:nat, o:nat.

sum (s X) Y (s Z) :- sum X Y Z.
sum z X X.
sum _ _ _ :-
  coq.error "nothing matched but for this catch all clause!".

}}.

Fail Elpi Query lp:{{ sum X (s z) Y }}.  (* .fails *)

(*|

The query fails because no rule first argument matches :e:`X`.

Instead of failing we can suspend goals and turn them into
syntactic constraints

|*)

Elpi Program peano3 lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred sum i:nat, i:nat, o:nat.

sum (s X) Y (s Z) :- sum X Y Z.
sum z X X.
sum X Y Z :-
  % the head of the rule always unifies with the query, so
  % we double check X is a variable (we could also be
  % here because the other rules failed)
  var X,
  % then we declare the constraint and schedule its resumption
  % on the assignment of X
  declare_constraint (sum X Y Z) [X].

}}.

Elpi Query lp:{{ sum X (s z) Z }}.

(*|

Syntactic constraints are resumed when the variable
they are suspended on is assigned:

|*)

Elpi Query lp:{{

  sum X (s z) Z, X = z,
  coq.say "The result is:" Z

}}.

(*|
  
Here a couple more examples. Keep in mind that:

* resumption can cause failure
* recall that :e:`;` stands for disjunction

|*)

Fail Elpi Query lp:{{ sum X (s z) (s (s z)),  X = z }}.  (* .fails *)
Elpi Query lp:{{ sum X (s z) (s (s z)), (X = z ; X = s z) }}.

(*|

In this example the computation suspends, then makes progress,
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

Elpi Query lp:{{ even (s X), odd (s X) }}. (* hum, not nice *)

(*|

-------------------------
Constraint Handling Rules
-------------------------

A constraint (handling) rule can see the store of syntactic constraints
as a whole, remove constraints and/or create new goals:

|*)

Elpi Accumulate lp:{{

constraint even odd {
  % if two distinct, conflicting, constraints about the same X
  % are part of the constraint store
  rule (even X) (odd X) <=>
   % generate the following goal
   (coq.say X "can't be even and odd at the same time", fail).
}

}}.

Fail Elpi Query lp:{{ even (s X), odd (s X) }}.  (* .fails *)

(*|

.. note:: :e:`fail` is a predicate with no solution

See also the Wikipedia page on `Constraint Handling Rules <https://en.wikipedia.org/wiki/Constraint_Handling_Rules>`_
for an introduction to the sub language to manipulate constraints.

.. _functional-style:

================
Functional style
================

Elpi is a relational language, not a functional one. Still some features
typical of functional programming are available, with some caveats.

-------------------------------
Spilling (relation composition)
-------------------------------

Chaining "relations" can be painful, especially when
they look like functions. Here we use :stdlib:`std.append`
and :stdlib:`std.rev` to build a palindrome:

|*)

Elpi Program function lp:{{

pred make-palindrome i:list A, o:list A.

make-palindrome L Result :-
  std.rev L TMP,
  std.append L TMP Result.

}}.

Elpi Query lp:{{

  make-palindrome [1,2,3] A

}}.

(*|

.. note:: variables (capital letters) can be used in
   types in order to describe ML-like polymorphism.

.. note:: :e:`list A` is a built-in data type

   The empty list is written :e:`[]`, while the cons constructor
   is written :e:`[Hd | Tail]`. Iterated cons can be written
   :e:`[ E1, E2 | Tail ]` and :e:`| Tail` can be omitted if the list
   is nil terminated.

The :e:`make-palindrome` predicate has to use a temporary variable
just to pass the output of a function as the input to another function.

Spilling is a syntactic elaboration which does that for you.
Expressions between `{` and `}` are
said to be spilled out and placed just before the predicate
that contains them.

*)

Elpi Accumulate lp:{{

pred make-palindrome2 i:list A, o:list A.

make-palindrome2 L Result :-
  std.append L {std.rev L} Result.

}}.

Elpi Query lp:{{

  make-palindrome2 [1,2,3] A

}}.

(*|

The two versions of :e:`make-palindrome` are equivalent.
Actually the latter is elaborated into the former. 

----------------------
APIs for built-in data
----------------------

Functions about built-in data types are available via the
:stdlib:`calc` predicate or its infix version :e:`is`. Example:

|*)

Elpi Query lp:{{

   calc ( "result " ^ "=" ) X,
   Y is 3 + 2,
   coq.say X Y 

}}.

(*|

The :stdlib:`calc` predicate works nicely with spilling:

|*)

Elpi Query lp:{{ coq.say "result =" {calc (2 + 3)} }}.

(*|
   
-----------------------
Allocation of variables
-----------------------

The language let's one use λ-abstraction also to write anonymous rules
but one has to be wary of where variables are bound (allocated really).

In our example we use the higher order predicate :stdlib:`std.map`:

.. code:: elpi

  pred std.map i:list A, i:(A -> B -> prop), o:list B.

.. note:: :e:`prop` is the type of predicates

   The actual type of the :e:`std.map` symbol is:

   .. code:: elpi
   
      type std.map list A -> (A -> B -> prop) -> list B -> prop.

   The :e:`pred` directive complements a type declaration for predicates
   (the trailing :e:`-> prop` is implicit) with a mode declaration for
   each argument.

The type of the second argument of :e:`std.map`
is the one of a predicate relating :e:`A` with :e:`B`.

Let's try to call :e:`std.map` passing an anonymous rule (as we
would do in a functional language by passing an anonymous function):

|*)

Elpi Accumulate lp:{{

pred bad i:list int, o:list int.

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
  good2 [1,2,3] R3

}}.

(*|

The problem with :e:`bad` is that :e:`TMP` is fresh each time the rule
is used, but not every time the anonymous rule passed to :stdlib:`map`
is used. Technically :e:`TMP` is quantified (allocated) where :e:`L`
and :e:`Result` are.

There are two ways to quantify :e:`TMP` correctly, that is inside the
anonymous predicate. One is to actually name the predicate. Another one is
to use the :e:`sigma x\ ` quantifier to allocate :e:`TMP` at every call.
We recommend to name the auxiliary predicate.

.. tip:: predicates whose name ends in `.aux` don't trigger a missing type
   declaration warning

One last way to skin the cat is to use :e:`=>` as follows. It gives us
the occasion to clarify further the scope of variables. 

|*)

Elpi Accumulate lp:{{

pred good3 i:list int, o:list int.
good3 L Result :-
  pi aux\
    (pi TMP X R\ aux X R :- TMP is X + 1, R = TMP) =>
    std.map L aux Result.

}}.

Elpi Query lp:{{

  good3 [1,2,3] R

}}.

(*|

In this case the auxiliary predicate :e:`aux`
is only visible inside :e:`good3`.
What is interesting to remark is that the quantifications are explicit
in the hypothetical rule, and they indicate clearly that each and every
time :e:`aux` is used :e:`TMP`, :e:`X` and :e:`R` are fresh.

The :e:`pi x\ ` quantifier is dual to :e:`sigma x\ `: since here it
occurs negatively it has the same meaning. That is, the hypothetical rule
could be written :e:`pi X R\ aux X R :- sigma TMP\ TMP is X + 1, R = TMP`.

.. tip:: :e:`pi x\ ` and :e:`sigma x\ ` can quantify on a bunch of variables
   at once

   That is, :e:`pi x y\ ...` is equivalent to :e:`pi x\ pi y\ ...` and
   :e:`sigma x y\ ...` is equivalent to :e:`sigma x\ sigma y\ ...`.

.. tip:: :e:`=>` can load more than one clause at once

   It is sufficient to put a list on the left hand side, eg :e:`[ rule1, rule2 ] => code`.
   Moreover one can synthesize a rule before loading it, eg:

   .. code:: elpi

      Rules = [ one-more-rule | ExtraRules ], Rules => code

The last remark worth making is that bound variables are intimately related
to universal quantification, while unification variables are related to
existential quantification.  It goes without saying that the following
two formulas are not equivalent and while the former is trivial the latter
is in general false:

.. math::

     ∀x, ∃Y, Y = x\\
     ∃Y, ∀x, Y = x

Let's run these two corresponding queries:

|*)

Elpi Query lp:{{ pi x\ sigma Y\ Y = x, coq.say "Y =" Y }}.
Fail Elpi Query lp:{{ sigma Y\ pi x\ Y = x, coq.say "Y =" Y }}.  (* .fails *)

(*|

Another way to put it: :e:`x` is in the scope of :e:`Y` only in the first
formula since it is quantified before it. Hence :e:`x` can be assigned to
:e:`Y` in that case, but not in the second query, where it is quantified
after.

More in general, λProlog tracks the bound variables that are in scope of each
unification variable. There are only two ways to put a bound variable
in the scope:

* quantify the unification variable under the bound one (first formula)
* pass the bound variable to the unification variable explicitly: in this
  case the unification variable needs to have a functional type.
  Indeed :math:`∃Y, ∀x, (Y x) = x` has a solution: :e:`Y` can be
  the identity function.

  .. coq::

     Elpi Query lp:{{ sigma Y\ pi x\ Y x = x, coq.say "Y =" Y }}.

If we look again at the rule for type checking
λ-abstraction:

.. code:: elpi

     of (fun F) (arr A B) :-
       pi x\ of x A => of (F x) B.

we can see that the only unification variable that sees the fresh
`x` is :e:`F`, because we pass :e:`x` to :e:`F` explicitly
(recall all unification variables such as :e:`F`, :e:`A`, :e:`B` are
quantified upfront, before the :e:`pi x\ `).
Indeed when we write:

.. math::

    \frac{\Gamma, x : A \vdash f : B}{\Gamma \vdash λx.f : A → B}

on paper, the variable denoted by :e:`x` being bound there can only occur in
:math:`f`, not in :math:`\Gamma` or :math:`B` for example (although a
*different* variable could be named the same, hence the usual freshness side
conditions which are not really necessary using HOAS).

Remark that in the premise the variable :math:`x` is still bound, this time
not by a λ-abstraction but by the context :math:`\Gamma, x : A`.
In λProlog the context is the set of hypothetical rules and :e:`pi\ `
-quantified variables and is implicitly handled by the runtime of the
programming language.

A slogan to keep in mind is that:

.. important::  There is no such thing as a free variable!

Indeed the variable bound by the λ-abstraction (of our data) is
replaced by a fresh variable bound by the context (of our program). This is
called binder mobility. See also the paper 
`Mechanized metatheory revisited <https://hal.inria.fr/hal-01884210/>`_ by
Dale Miller which is an excellent
introduction to these concepts.

=========
Debugging
=========

The most sophisticated debugging feature can be used via
the Visual Studio Code extension ``gares.elpi-lang`` and its
``Elpi Tracer`` tab.

---------------
Trace browser
---------------
   
In order to generate a trace one needs to execute the
``Elpi Trace Browser.`` command and then run any Elpi code.

|*)

(* Elpi Trace Browser. *)

Elpi Query stlc lp:{{ % We run the query in the stlc program

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

(*|

The trace file is generated in ``/tmp/traced.tmp.json``. 
If it does not load automatically one can do it manually by clicking on
the load icon, in the upper right corner of the Elpi Tracer panel.

.. note:: partial display of goals

   At the time of writing one may need to disable syntax highlighting in
   the extension settings in order to get a correct display.

The trace browser displays, on the left column, a list of cards corresponding
to a step performed by the interpreter. The right side of the
panel gives more details about the selected step. In the image below one
can see the goal, the rule being applied, the assignments performed by the
unification of the rule's head with the goal, the subgoals generated.

.. image:: tracer.png
   :width: 800

One can also look at the trace in text format (if VSCode is not an option,
for example).

|*)
Elpi Trace.

Elpi Query stlc lp:{{ % We run the query in the stlc program

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

Fail Elpi Query stlc lp:{{

  of (fun (x\ app x x)) Ty, coq.say Ty

}}.  (* .fails *)

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

---------------
Good old print
---------------

A common λProlog idiom is to have a debug rule
lying around.  The :e:`:if` attribute can be used to
make the rule conditionally interpreted (only if the
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

------------------------
Printing entire programs
------------------------
   
Given that programs are not written in a single place, but rather obtained by
accumulating code, Elpi is able to print a (full) program to an html file
as follows. The obtained file provides a facility to filter rules by their
predicate. 

|*)

Elpi Print stlc "elpi_examples/stlc".

(*|

Look at the `generated page <https://lpcic.github.io/coq-elpi/stlc.html>`_
and type :e:`of` in the filter.

Finally, one can bound the number of backchaining steps
performed by the interpreter:

|*)

Elpi Query lp:{{ 0 = 0, 1 = 1 }}.
Elpi Bound Steps 1.
Fail Elpi Query lp:{{ 0 = 0, 1 = 1 }}. (* .fails *) (* it needs 2 steps! *)
Elpi Bound Steps 0. (* Go back to no bound *)

(*|

---------------
Common pitfalls
---------------

Well, no programming language is perfect.

++++++++++++++++++++++++++++++++
Precedence of :e:`,` and :e:`=>`
++++++++++++++++++++++++++++++++


The precedence of :e:`,` and :e:`=>` can be surprising

|*)

Fail Elpi Query stlc lp:{{

   pi x\
     of x A => of x B, of x C

}}. (* .fails *)

Elpi Query stlc lp:{{

  pi x\
    of x A => (of x B, of x C) % both goals see of x A

}}.

(*|

++++++++++++
Backtracking
++++++++++++


Backtracking can lead to weird execution traces. The :stdlib:`std.do!` predicate
should be used to write non-backtracking code.

.. code:: elpi

   pred not-a-backtracking-one.
   not-a-backtracking-one :- condition, !, std.do! [
     step,
     (generate, test),
     step,
   ].

In the example above once :e:`condition` holds we start a sequence of
steps which we will not reconsider. Locally, backtracking is still
available, e.g. between :e:`generate` and :e:`test`.
See also the :stdlib:`std.spy-do!` predicate which prints each and every step,
and the :stdlib:`std.spy` one which can be used to spy on a single one.

+++++++++++++++++++++++++++++++++++++++++++++++
Unification variables v.s. Imperative variables
+++++++++++++++++++++++++++++++++++++++++++++++

Unification variables sit in between variables in imperative programming and
functional programming. In imperative programming a variable can hold a value,
and that value can change over time via assignment. In functional languages
variables always hold a value, and that value never changes. In logic programming
a unification variable can either be unset (no value) or set to a value that
never changes. Backtracking goes back in time, it is not visible to the program.

As a result of this, code like

.. code:: elpi

   pred bad-example.
   bad-example :- X is 1 + 2, X is 4 + 5.
   
fails, because :e:`X` cannot be at the same time 3 and 9. Initially
:e:`X` is unset, then it is set to 3, and finally the programmer is
asserting that 3 (the value hold by :e:`X`) is equal to 9.
The second call to :e:`is` does not change the value carried by :e:`X`!
   
Unification, and hence the :e:`=` predicate, plays two roles.
When :e:`X` is unset, :e:`X = v` sets the variable.
When :e:`X` is set to :e:`u`, :e:`X = v` checks if the value
of :e:`X` is equal to :e:`u`: it is equivalent to  :e:`u = v`.

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


