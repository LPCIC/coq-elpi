Writing commands in Elpi
============================

.. seealso::
   An `Alectryon-rendered version
   <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html>`_ of
   this tutorial (together with :doc:`coq-commands-advanced`), from before
   its migration to this manual, is also available.

This tutorial assumes the reader is familiar with Elpi and the HOAS
representation of Rocq terms; if it is not the case, please take a look at
these other tutorials first: :doc:`elpi-lang` and :doc:`coq-hoas`.

.. contents::

Defining commands
---------------------

Let's create a simple command, called "hello", which prints :e:`"Hello"`
followed by the arguments we pass to it:

.. rocqtop:: none reset

   Set Warnings "-elpi.linear-variable".

.. rocqtop:: all

   From elpi Require Import elpi.

   Elpi Command hello.
   Elpi Accumulate lp:{{

     % main is, well, the entry point
     main Arguments :- coq.say "Hello" Arguments.

   }}.

The program declaration is made of 3 parts.

The first one ``Elpi Command hello.`` sets the current program to hello.
Since it is declared as a ``Command`` some code is loaded automatically:

* APIs (eg :builtin:`coq.say`) and data types (eg Rocq :type:`term` s) are loaded from
  `coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin.elpi>`_
* some utilities, like :lib:`copy` or :libred:`whd1` are loaded from
  `elpi-command-template.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template.elpi>`_

The second one ``Elpi Accumulate ...`` loads some extra code.
The ``Elpi Accumulate ...`` family of commands lets one accumulate code
taken from:

* verbatim text ``Elpi Accumulate lp:{{ code }}``
* source files ``Elpi Accumulate File path``
* data bases (Db) ``Elpi Accumulate Db name``

Accumulating code via inline text or file is equivalent, the AST of ``code``
is stored in the .vo file (the external file does not need to be installed).
We postpone the description of data bases to a dedicated section.

When some code is accumulated Elpi verifies that the
code does not contain the most frequent kind of mistakes, via some
type checking and linting. Some mistakes are minor and Elpi only warns about
them. You can pass ``-w +elpi.typecheck`` to ``coqc`` to turn these warnings into
errors.

We can now run our program!

.. rocqtop:: all
   :assert: str world!

   Elpi hello "world!".

You should see the captured output above. The string ``"world!"`` we passed
to the command is received by the code as :e:`(str "world!")`.

.. note:: :builtin:`coq.say` won't print quotes around strings

Command arguments
---------------------

Let's pass different kind of arguments to ``hello``:

.. rocqtop:: all

   Elpi hello 46.
   Elpi hello there.

This time we passed to the command a number and an identifier.
Identifiers are received as strings, and can contain dots, but no spaces.

.. rocqtop:: all

   Elpi hello my friend.
   Elpi hello this.is.a.qualified.name.

Indeed the first invocation passes two arguments, of type string, while
the second a single one, again a string containing dots.

There are a few more types of arguments a command can receive:

* terms, delimited by ``(`` and ``)``
* toplevel declarations, like ``Inductive ..``, ``Definition ..``, etc..
  which are introduced by their characterizing keyword.

Let's try with a term.

.. rocqtop:: all

   Elpi hello (0 = 1).

Since Rocq-Elpi 1.15, terms are received in elaborated form, meaning
that the elaborator of Rocq is used to pre-process them.
In the example above the type argument to ``eq`` has
been synthesized to be ``nat``.

.. rocqtop:: all

   Elpi hello Definition test := 0 = 1.
   Elpi hello Record test := { f1 : nat; f2 : f1 = 1 }.

Global declarations are received in elaborated form as well.
In the case of ``Definition test`` the optional body (would be
:e:`none` for an ``Axiom`` declaration) is present
while the omitted type is inferred (to be ``Prop``).

In the case of the ``Record`` declaration remark that each field has a few
attributes, like being a coercions (the ``:>`` in Rocq's syntax). Also note that
the type of the record (which was omitted) defaults to ``Type``.
Finally note that the type of the second field
sees :e:`c0` (the value of the first field).

See the :type:`argument` data type
for a detailed description of all the arguments a command can receive.

Processing raw arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is sometimes useful to receive arguments in raw format,
so that no elaboration has been performed.
This can be achieved by using the
``#[arguments(raw)]`` attributed when the command is declared.

Then, there are two ways to process term arguments:
typechecking and elaboration.

.. rocqtop:: all

   #[arguments(raw)] Elpi Command check_arg.
   Elpi Accumulate lp:{{

     main [trm T] :-
       std.assert-ok! (coq.typecheck T Ty) "argument illtyped",
       coq.say "The type of" T "is" Ty.

   }}.

   Elpi check_arg (1 = 0).
   Fail Elpi check_arg (1 = true).

The command ``check_arg`` receives a term :e:`T` and type checks it, then it
prints the term and its type.

The :builtin:`coq.typecheck` API has 3 arguments: a term, its type and a
:stdtype:`diagnostic` which can either be :e:`ok` or :e:`(error Message)`.
The :stdlib:`assert-ok!` combinator checks if the diagnostic is :e:`ok`,
and if not it prints the error message and bails out.

The first invocation succeeds while the second one fails and prints
the type checking error (given by Rocq) following the string passed to
:e:`std.assert-ok!`.

.. rocqtop:: all

   Coercion bool2nat (b : bool) := if b then 1 else 0.
   Fail Elpi check_arg (1 = true).
   Check (1 = true).

The command still fails even if we told Rocq how to inject booleans values
into the natural numbers. Indeed the ``Check`` commands works.

The call to :builtin:`coq.typecheck` modifies the term in place, it can assign
implicit arguments (like the type parameter of ``eq``) but it cannot modify the
structure of the term. To do so, one has to use the
:builtin:`coq.elaborate-skeleton` API.

.. rocqtop:: all

   #[arguments(raw)]
   Elpi Command elaborate_arg.
   Elpi Accumulate lp:{{

     main [trm T] :-
       std.assert-ok! (coq.elaborate-skeleton T Ty T1) "illtyped arg",
       coq.say "T=" T,
       coq.say "T1=" T1,
       coq.say "Ty=" Ty.

   }}.

   Elpi elaborate_arg (1 = true).

Remark how :e:`T` is not touched by the call to this API, and how :e:`T1`
is a copy of :e:`T` where the hole after ``eq`` is synthesized and the value
``true`` injected to ``nat`` by using ``bool2nat``.

It is also possible to manipulate term arguments before typechecking
them, but note that all the considerations on holes in the tutorial about
the HOAS representation of Rocq terms apply here. An example of tool
taking advantage of this possibility is Hierarchy Builder: the declarations
it receives would not typecheck in the current context, but do once the
context is temporarily augmented with ad-hoc canonical structure instances.

Examples
-----------

Synthesizing a term
~~~~~~~~~~~~~~~~~~~~~~

Synthesizing a term typically involves reading an existing declaration
and writing a new one. The relevant APIs are in the ``coq.env.*`` namespace
and are named after the global reference they manipulate, eg :builtin:`coq.env.const`
for reading and :builtin:`coq.env.add-const` for writing.

Here we implement a little command that given an inductive type name
generates a term of type ``nat`` whose value is the number of constructors
of the given inductive type.

.. rocqtop:: all

   Elpi Command constructors_num.

   Elpi Accumulate lp:{{

   pred int->nat int -> term.
   int->nat 0 {{ 0 }}.
   int->nat N {{ S lp:X }} :- M is N - 1, int->nat M X.

   main [str IndName, str Name] :-
     std.assert! (coq.locate IndName (indt GR)) "not an inductive type",
     coq.env.indt GR _ _ _ _ Kn _,      % the names of the constructors
     std.length Kn N,                   % count them
     int->nat N Nnat,                   % turn the integer into a nat
     coq.env.add-const Name Nnat _ _ _. % save it

   }}.

   Elpi constructors_num bool nK_bool.
   Print nK_bool.

   Elpi constructors_num False nK_False.
   Print nK_False.

   Fail Elpi constructors_num plus nK_plus.
   Fail Elpi constructors_num not_there bla.

The command starts by locating the first argument and asserting it points to
an inductive type. This line is idiomatic: :builtin:`coq.locate` aborts if
the string cannot be located, and if it relates it to a :e:`gref` which is not
:e:`indt` (for example :e:`const plus`) :stdlib:`assert!` aborts with the given
error message.

:builtin:`coq.env.indt` lets one access all the details of an inductive type,
here we just use the list of constructors.
The twin API :builtin:`coq.env.indt-decl` lets
one access the declaration of the inductive in HOAS form, which might be
easier to manipulate in other situations, like the next example.

Then the program crafts a natural number and declares a constant for it.

Abstracting an inductive
~~~~~~~~~~~~~~~~~~~~~~~~~~~

For the sake of introducing :lib:`copy`, the swiss army knife of λProlog, we
write a command which takes an inductive type declaration and builds a new
one abstracting the former one on a given term. The new inductive has a
parameter in place of the occurrences of that term.

.. rocqtop:: all

   Elpi Command abstract.

   Elpi Accumulate lp:{{

     % a renaming function which adds a ' to an ident (a string)
     pred prime id -> id.
     prime S S1 :- S1 is S ^ "'".

     pred id id -> id.
     id X X.

     main [str Ind, trm Param] :-

       % the term to be abstracted out, P of type PTy
       std.assert-ok!
         (coq.elaborate-skeleton Param PTy P)
         "illtyped parameter",

       % fetch the old declaration
       std.assert! (coq.locate Ind (indt I)) "not an inductive type",
       coq.env.indt-decl I Decl,

       % let's start to craft the new declaration by putting a
       % parameter A which has the type of P
       (NewDecl : indt-decl) = parameter "A" explicit PTy Decl',

       % let's make a copy, capturing all occurrences of P with a
       % (which stands for the parameter)
       (pi a\ (copy P a :- !) ==> copy-indt-decl Decl (Decl' a)),

       % to avoid name clashes, we rename the type and its constructors
       % (we don't need to rename the parameters)
       coq.rename-indt-decl id prime prime NewDecl DeclRenamed,

       % we type check the inductive declaration, since abstracting
       % random terms may lead to illtyped declarations (type theory
       % is hard)
       std.assert-ok!
         (coq.typecheck-indt-decl DeclRenamed)
         "can't be abstracted",

       coq.env.add-indt DeclRenamed _.

   }}.

   Inductive tree := leaf | node : tree -> option nat -> tree -> tree.

   Elpi abstract tree (option nat).
   Print tree'.

As expected ``tree'`` has a parameter ``A``.

Now let's focus on :lib:`copy`. The standard
coq library (loaded by the command template) contains a definition of copy
for terms and declarations.

An excerpt:

.. code-block:: elpi

  copy X X :- name X.      % checks X is a bound variable
  copy (global _ as C) C.
  copy (fun N T F) (fun N T1 F1) :-
    copy T T1, pi x\ copy (F x) (F1 x).
  copy (app L) (app L1) :- std.map L copy L1.

:e:`copy` implements the identity: it builds, recursively, a copy of the first
term into the second argument. Unless one loads in the context a new rule,
which takes precedence over the identity ones. Here we load:

.. code-block:: elpi

  copy P a

which, at run time, looks like

.. code-block:: elpi

  copy (app [global (indt «option»), global (indt «nat»)]) c0

and that rule masks the one for ``app`` when the sub-term being copied is
exactly ``option nat``. The API :lib:`copy-indt-decl` copies an inductive
declaration and calls ``copy`` on all the terms it contains (e.g. the
type of the constructors).

The :lib:`copy` predicate is very flexible, but sometimes one needs to collect
some data along the way. The sibling API :lib:`fold-map` lets one do that.

An excerpt:

.. code-block:: elpi

  fold-map (fun N T F) A (fun N T1 F1) A2 :-
    fold-map T A T1 A1, pi x\ fold-map (F x) A1 (F1 x) A2.

For example one can use :lib:`fold-map` to collect into a list all the occurrences
of inductive type constructors in a given term, then use the list to postulate
the right number of binders for them, and finally use :lib:`copy` to capture them.

Using DBs to store data across calls
----------------------------------------

A Db can be created with the command:

.. rocqtop:: all

   Elpi Db name.db lp:{{ pred some-pred. }}.

and a Db can be later extended via ``Elpi Accumulate``.
As a convention, we like Db names to end in a .db suffix.

A Db is pretty much like a regular program but can be *shared* among
other programs and is accumulated *by name*.
Since is a Db is accumulated *when a program runs* the *current
contents of the Db are used*.
Moreover the Db can be extended by Elpi programs themselves
thanks to the API :builtin:`coq.elpi.accumulate`, enabling code to save a state
which is then visible at subsequent runs.

The initial contents of a Db, ``pred some-pred.`` in the example
above, is usually just the type declaration for the predicates part of the Db,
and maybe a few default rules.
Let's define a Db.

.. rocqtop:: all

   Elpi Db age.db lp:{{

     % A typical Db is made of one main predicate
     pred age -> string, int.

     % the Db is empty for now, we put a rule giving a
     % descriptive error and we name that rule "age.fail".
     :name "age.fail"
     age Name _ :- coq.error "I don't know who" Name "is!".

   }}.

Elpi rules can be given a name via the :e:`:name` attribute. Named rules
serve as anchor-points for new rules when added to the Db.

Let's define a ``Command`` that makes use of a Db.

.. rocqtop:: all

   Elpi Command age.
   Elpi Accumulate Db age.db.  (* we accumulate the Db *)
   Elpi Accumulate lp:{{

     main [str Name] :-
       age Name A,
       coq.say Name "is" A "years old".

   }}.

   Fail Elpi age bob.

Let's put some data in the Db. Given that the Db contains a catch-all rule,
we need the new ones to be put before it.

.. rocqtop:: all

   Elpi Accumulate age.db lp:{{

     :before "age.fail"     % we place this rule before the catch all
     age "bob" 24.

   }}.

   Elpi age bob.

Extending data bases this way is fine, but requires the user of our command
to be familiar with Elpi's syntax, which is not very nice. Instead,
we can write a new program that uses the :builtin:`coq.elpi.accumulate` API
to extend the Db.

.. rocqtop:: all

   Elpi Command set_age.
   Elpi Accumulate Db age.db.
   Elpi Accumulate lp:{{
     main [str Name, int Age] :-
       TheNewRule = age Name Age,
       coq.elpi.accumulate _ "age.db"
         (clause _ (before "age.fail") TheNewRule).

   }}.

   Elpi set_age "alice" 21.
   Elpi age "alice".

Additions to a Db are a Rocq object, a bit like a Notation or a Type Class
instance: these object live inside a Rocq module (or a Rocq file) and become
active when that module is Imported.

Deciding to which Rocq module these
extra rules belong is important and :builtin:`coq.elpi.accumulate` provides
a few options to tune that. Here we passed :e:`_`, that uses the default
setting. See the :type:`scope` and :type:`clause` data types for more info.

Inspecting a Db
~~~~~~~~~~~~~~~~~~

So far we did query a Db but sometimes one needs to inspect the whole
contents.

.. rocqtop:: all

   Elpi Command print_all_ages.
   Elpi Accumulate Db age.db.
   Elpi Accumulate lp:{{

     :before "age.fail"
     age _ _ :- !, fail. % softly

     main [] :-
       std.findall (age _ _) Rules,
       std.forall Rules print-rule.

     pred print-rule (pred).
     print-rule (age P N) :- coq.say P "is" N "years old".

   }}.

   Elpi print_all_ages.

The :stdlib:`std.findall` predicate gathers in a list all solutions to
a query, while :stdlib:`std.forall` iterates a predicate over a list.
It is important to notice that :builtin:`coq.error` is a fatal error which
aborts an Elpi program. Here we shadow the catch all clause with a regular
failure so that :stdlib:`std.findall` can complete to list all the results.

Continue with :doc:`coq-commands-advanced`.
