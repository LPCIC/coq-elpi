(*|

Tutorial on Coq commands
************************

:author: Enrico Tassi

.. include:: ../etc/tutorial_style.rst

..
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
   exposing to the extension language Coq specific data types (e.g. terms)
   and API (e.g. to declare a new inductive type).
   
   In order to get proper syntax highlighting using VSCode please install the
   "gares.coq-elpi-lang" extension. In CoqIDE please chose "coq-elpi" in
   Edit -> Preferences -> Colors.

This tutorial assumes the reader is familiar with Elpi and the HOAS
representation of Coq terms; if it is not the case, please take a look at
these other tutorials first:
`Elpi tutorial <https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html>`_
and 
`Coq HOAS tutorial <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html>`_.

.. contents::

=================
Defining commands
=================

Let's create a simple command, called "hello", which prints :e:`"Hello"`
followed by the arguments we pass to it:

|*)
From elpi Require Import elpi.

Elpi Command hello.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "Hello" Arguments.

}}.


(*|

The program declaration is made of 3 parts.

The first one `Elpi Command hello.` sets the current program to hello.
Since it is declared as a `Command` some code is loaded automatically:

* APIs (eg :builtin:`coq.say`) and data types (eg Coq :type:`term` s) are loaded from
  `coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin.elpi>`_
* some utilities, like :lib:`copy` or :libred:`whd1` are loaded from
  `elpi-command-template.elpi <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template.elpi>`_

  
The second one `Elpi Accumulate ...` loads some extra code.
The `Elpi Accumulate ...` family of commands lets one accumulate code
taken from:

* verbatim text `Elpi Accumulate lp:{{ code }}`
* source files `Elpi Accumulate File path`
* data bases (Db) `Elpi Accumulate Db name`

Accumulating code via inline text or file is equivalent, the AST of `code`
is stored in the .vo file (the external file does not need to be installed).
We postpone the description of data bases to a dedicated section.

When some code is accumulated Elpi verifies that the
code does not contain the most frequent kind of mistakes, via some
type checking and linting. Some mistakes are minor and Elpi only warns about
them. You can pass `-w +elpi.typecheck` to `coqc` to turn these warnings into
errors.

We can now run our program!

|*)

Elpi hello "world!".

(*|

You should see the following output (hover the bubble next to the
code if you are reading this online):

.. mquote:: .s(Elpi hello).msg(str world)
   :language: text

The  string `"world!"` we passed to the command is received by the code
as :e:`(str "world!")`. 

.. note:: :builtin:`coq.say` won't print quotes around strings

=================
Command arguments
=================

Let's pass different kind of arguments to `hello`:

|*)

Elpi hello 46.
Elpi hello there.

(*|

This time we passed to the command a number and an identifier.
Identifiers are received as strings, and can contain dots, but no spaces.

|*)

Elpi hello my friend.
Elpi hello this.is.a.qualified.name.

(*|

Indeed the first invocation passes two arguments, of type string, while
the second a single one, again a string containing dots.

There are a few more types of arguments a command can receive:

* terms, delimited by `(` and `)`
* toplevel declarations, like `Inductive ..`, `Definition ..`, etc..
  which are introduced by their characterizing keyword.

Let's try with a term.

|*)

Elpi hello (0 = 1).

(*|

Since Coq-Elpi 1.15, terms are received in elaborated form, meaning
that the elaborator of Coq is used to pre-process them.
In the example above the type argument to `eq` has
been synthesized to be `nat`.

|*)

Elpi hello Definition test := 0 = 1.
Elpi hello Record test := { f1 : nat; f2 : f1 = 1 }.

(*|

Global declarations are received in elaborated form as well.
In the case of `Definition test` the optional body (would be
:e:`none` for an `Axiom` declaration) is present
while the omitted type is inferred (to be `Prop`).

In the case of the `Record` declaration remark that each field has a few
attributes, like being a coercions (the `:>` in Coq's syntax). Also note that
the type of the record (which was omitted) defaults to `Type`.
Finally note that the type of the second field
sees :e:`c0` (the value of the first field).

See the :type:`argument` data type
for a detailed description of all the arguments a command can receive.

------------------------
Processing raw arguments
------------------------

It is sometimes useful to receive arguments in raw format, 
so that no elaboration has been performed.
This can be achieved by using the 
`#[arguments(raw)]` attributed when the command is declared.

Then, there are two ways to process term arguments:
typechecking and elaboration.
    
|*)

#[arguments(raw)] Elpi Command check_arg.
Elpi Accumulate lp:{{

  main [trm T] :-
    std.assert-ok! (coq.typecheck T Ty) "argument illtyped",
    coq.say "The type of" T "is" Ty.

}}.


Elpi check_arg (1 = 0).
Fail Elpi check_arg (1 = true). (* .fails *)

(*|

The command `check_arg` receives a term :e:`T` and type checks it, then it
prints the term and its type.

The :builtin:`coq.typecheck` API has 3 arguments: a term, its type and a
:stdtype:`diagnostic` which can either be :e:`ok` or :e:`(error Message)`.
The :stdlib:`assert-ok!` combinator checks if the diagnostic is :e:`ok`,
and if not it prints the error message and bails out.
  
The first invocation succeeds while the second one fails and prints
the type checking error (given by Coq) following the string passed to
:e:`std.assert-ok!`.

|*)

Coercion bool2nat (b : bool) := if b then 1 else 0.
Fail Elpi check_arg (1 = true).  (* .fails *)
Check (1 = true).

(*|

The command still fails even if we told Coq how to inject booleans values
into the natural numbers. Indeed the `Check` commands works.

The call to :builtin:`coq.typecheck` modifies the term in place, it can assign
implicit arguments (like the type parameter of `eq`) but it cannot modify the
structure of the term. To do so, one has to use the
:builtin:`coq.elaborate-skeleton` API.

|*)

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

(*|

Remark how :e:`T` is not touched by the call to this API, and how :e:`T1`
is a copy of :e:`T` where the hole after `eq` is synthesized and the value
`true` injected to `nat` by using `bool2nat`.

It is also possible to manipulate term arguments before typechecking
them, but note that all the considerations on holes in the tutorial about
the HOAS representation of Coq terms apply here. An example of tool
taking advantage of this possibility is Hierarchy Builder: the declarations
it receives would not typecheck in the current context, but do once the
context is temporarily augmented with ad-hoc canonical structure instances.

========
Examples
========

-------------------
Synthesizing a term
-------------------

Synthesizing a term typically involves reading an existing declaration
and writing a new one. The relevant APIs are in the `coq.env.*` namespace
and are named after the global reference they manipulate, eg :builtin:`coq.env.const`
for reading and :builtin:`coq.env.add-const` for writing.

Here we implement a little command that given an inductive type name
generates a term of type `nat` whose value is the number of constructors
of the given inductive type.

|*)

Elpi Command constructors_num.

Elpi Accumulate lp:{{

pred int->nat i:int, o:term.
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

Fail Elpi constructors_num plus nK_plus. (* .fails *)
Fail Elpi constructors_num not_there bla. (* .fails *)

(*|

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

------------------------
Abstracting an inductive
------------------------

For the sake of introducing :lib:`copy`, the swiss army knife of λProlog, we
write a command which takes an inductive type declaration and builds a new
one abstracting the former one on a given term. The new inductive has a
parameter in place of the occurrences of that term.

|*)

Elpi Command abstract.

Elpi Accumulate lp:{{

  % a renaming function which adds a ' to an ident (a string)
  pred prime i:id, o:id.
  prime S S1 :- S1 is S ^ "'".

  pred id i:id, o:id.
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
    (pi a\ copy P a ==> copy-indt-decl Decl (Decl' a)),

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

(*|

As expected `tree'` has a parameter `A`.

Now let's focus on :lib:`copy`. The standard
coq library (loaded by the command template) contains a definition of copy
for terms and declarations.

An excerpt:

.. code:: elpi

  copy X X :- name X.      % checks X is a bound variable
  copy (global _ as C) C.
  copy (fun N T F) (fun N T1 F1) :-
    copy T T1, pi x\ copy (F x) (F1 x).
  copy (app L) (app L1) :- std.map L copy L1.

:e:`copy` implements the identity: it builds, recursively, a copy of the first
term into the second argument. Unless one loads in the context a new rule,
which takes precedence over the identity ones. Here we load:

.. code:: elpi

  copy P a

which, at run time, looks like

.. code:: elpi

  copy (app [global (indt «option»), global (indt «nat»)]) c0

and that rule masks the one for `app` when the sub-term being copied is
exactly `option nat`. The API :lib:`copy-indt-decl` copies an inductive
declaration and calls `copy` on all the terms it contains (e.g. the
type of the constructors).

The :lib:`copy` predicate is very flexible, but sometimes one needs to collect
some data along the way. The sibling API :lib:`fold-map` lets one do that.

An excerpt:

.. code:: elpi

  fold-map (fun N T F) A (fun N T1 F1) A2 :-
    fold-map T A T1 A1, pi x\ fold-map (F x) A1 (F1 x) A2.

For example one can use :lib:`fold-map` to collect into a list all the occurrences
of inductive type constructors in a given term, then use the list to postulate
the right number of binders for them, and finally use :lib:`copy` to capture them.


====================================
Using DBs to store data across calls
====================================

A Db can be created with the command:

|*)

Elpi Db name.db lp:{{ pred some-pred. }}.

(*|

and a Db can be later extended via `Elpi Accumulate`.
As a convention, we like Db names to end in a .db suffix.

A Db is pretty much like a regular program but can be *shared* among
other programs and is accumulated *by name*.
Since is a Db is accumulated *when a program runs* the *current
contents of the Db are used*.
Moreover the Db can be extended by Elpi programs themselves
thanks to the API :builtin:`coq.elpi.accumulate`, enabling code to save a state
which is then visible at subsequent runs.

The initial contents of a Db, `pred some-pred.` in the example
above, is usually just the type declaration for the predicates part of the Db,
and maybe a few default rules.
Let's define a Db.

|*)

Elpi Db age.db lp:{{

  % A typical Db is made of one main predicate
  pred age o:string, o:int.

  % the Db is empty for now, we put a rule giving a
  % descriptive error and we name that rule "age.fail".
  :name "age.fail"
  age Name _ :- coq.error "I don't know who" Name "is!".

}}.

(*|

Elpi rules can be given a name via the :e:`:name` attribute. Named rules
serve as anchor-points for new rules when added to the Db.

Let's define a `Command` that makes use of a Db.

|*)

Elpi Command age.
Elpi Accumulate Db age.db.  (* we accumulate the Db *)
Elpi Accumulate lp:{{

  main [str Name] :-
    age Name A,
    coq.say Name "is" A "years old".

}}.
 

Fail Elpi age bob.  (* .fails *)

(*|

Let's put some data in the Db. Given that the Db contains a catch-all rule,
we need the new ones to be put before it.
   
|*)

Elpi Accumulate age.db lp:{{

  :before "age.fail"     % we place this rule before the catch all
  age "bob" 24.

}}.

Elpi age bob.

(*|

Extending data bases this way is fine, but requires the user of our command
to be familiar with Elpi's syntax, which is not very nice. Instead,
we can write a new program that uses the :builtin:`coq.elpi.accumulate` API
to extend the Db.

|*)

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

(*|
  
Additions to a Db are a Coq object, a bit like a Notation or a Type Class
instance: these object live inside a Coq module (or a Coq file) and become
active when that module is Imported.

Deciding to which Coq module these
extra rules belong is important and :builtin:`coq.elpi.accumulate` provides
a few options to tune that. Here we passed :e:`_`, that uses the default
setting. See the :type:`scope` and :type:`clause` data types for more info.

.. _inspecting:

---------------
Inspecting a Db
---------------

So far we did query a Db but sometimes one needs to inspect the whole
contents.

|*)

Elpi Command print_all_ages.
Elpi Accumulate Db age.db.
Elpi Accumulate lp:{{

  :before "age.fail"
  age _ _ :- !, fail. % softly

  main [] :-
    std.findall (age _ _) Rules,
    std.forall Rules print-rule.

  pred print-rule i:prop.
  print-rule (age P N) :- coq.say P "is" N "years old".
  
}}.

Elpi print_all_ages.

(*|

The :stdlib:`std.findall` predicate gathers in a list all solutions to
a query, while :stdlib:`std.forall` iterates a predicate over a list.
It is important to notice that :builtin:`coq.error` is a fatal error which
aborts an Elpi program. Here we shadow the catch all clause with a regular
failure so that :stdlib:`std.findall` can complete to list all the results.

===================
Polishing a command
===================

The details do make the difference, some times.

----------
Attributes
----------

Elpi programs can be prefixed with attributes, like `#[local]`.
Attributes are not passed as arguments but rather as a rule in the context,
a bit like the option :e:`@holes!` we have seen before.
   
|*)

Elpi Command attr.
Elpi Accumulate lp:{{

  main _ :-
    attributes A, % we fetch the list of attributes from the context
    coq.say A.

}}.

#[this, more(stuff="33")] Elpi attr.

(*|

The first attribute, :e:`elpi.loc` is always present and corresponds to the
location in the source file of the command. Then we find an attribute for
:e:`"this"` holding the empty string and an attribute for :e:`"more.stuff"` holding
the string :e:`"33"`.

Attributes are usually validated (parsed) and turned into regular options
using :lib-common:`coq.parse-attributes` and a description of their types using 
the :libtype-common:`attribute-type` data type:

|*)

Elpi Command parse_attr.
Elpi Accumulate lp:{{

  pred some-code.
  some-code :-
    get-option "more.stuff" N, get-option "this" B, coq.say N B.

  main _ :-
    attributes A,
    coq.parse-attributes A [
      att "this" bool,
      att "more.stuff" int,
    ] Opts,
    coq.say "options=" Opts,
    Opts ==> some-code.

}}.
#[this, more(stuff="33")] Elpi parse_attr.
Fail #[unknown] Elpi parse_attr.  (* .fails *)

(*|

Note that :e:`get-option` links a string with a datum of type :e:`any`, which means
no type checking is performed on it. It is recommended to wrap calls to
get-option into other predicates typed in a more precise way. Eg:

.. code:: elpi

   pred get-my-option o:int.
   get-my-option I :- get-option "my-option-name" I.

-----------------------------
Extending the command grammar
-----------------------------

Elpi programs can be exported as regular Coq commands, so that the
final user does not need to type `Elpi` to invoke them.

|*)

Elpi Command Say.
Elpi Accumulate lp:{{ main [str S] :- coq.say S. }}.


Elpi Export Say. (* extend the Coq command grammar *)

Say "That is all folks!".

(*|

Not yet...

Coq offers no equivalent of `Tactic Notation` for commands.
Still Elpi commands accept any symbol or keyword as strings.
It is up to the programmer to catch and report parse errors.

|*)

Elpi Command Go.
Elpi Accumulate lp:{{
  main [str Src, str "=>", str Tgt, str "/", str F] :- !,
    coq.say "going from" Src "to" Tgt "via" F.
  main _ :-
    coq.error "Parse error! Use: go <from> => <to> / <via>".
}}.

Elpi Export Go.

Go source => target / plane.
Fail Go nowhere.  (* .fails *)

(*|

----------------
Reporting errors
----------------

Last, (good) Elpi programs should fail reporting intelligible error messages,
as the previous one.

|*)

Elpi Command bad.
Elpi Accumulate lp:{{ main []. }}.

Elpi Export bad.

Fail bad 1.  (* .fails *)

(*|

If they just fail, they produce the following generic
error:

.. mquote:: .s(bad 1).msg(inconvenience)
   :language: text

You should use the :builtin:`coq.error` API or the :stdlib:`assert!` one
to abort a program. There is a dedicated :builtin:`coq.ltac.fail` API to abort
tactics.

Warnings can be reported using the :builtin:`coq.warning` which lets you
pick a name and category. In turn these can be used to disable or make fatal
your warnings (as any other Coq warning).

=====================
Parsing and Execution
=====================

Since version 8.18 Coq has separate parsing and execution phases,
respectively called synterp and interp.

Since Coq has an extensible grammar the parsing phase is not entirely
performed by the parser: after parsing one sentence Coq evaluates its
synterp action. The synterp actions of a command like `Import A.` are
the subset of its effect which affect parsing, like enabling a notation.
Later, during the execution phase, Coq evaluates its
interp actions, which include effects like putting lemma in scope or
enabling type class instances etc. Synterp actions are quick, if only because
they don't really manipulate Coq terms, hence no type checking and the like.

Being able to parse an entire document quickly
is important for developing reactive
user interfaces, but requires some extra work when defining new commands,
in particular to identify their synterp.
Each command defined with Coq-Elpi is split into two programs,
one running during the parsing phase and the other one during the execution
phase. Each API that affects the parser, i.e. APIs dealing with modules
and sections like begin/end-module or import/export, is available to both the
synterp and the interp program under the same name, but its actual effect is
limited to what concerns the current phase. Hence all these APIs have to be
called at *both* synterp and interp time and *in the same order*.

At synterp time the data types and the APIs are restricted, in particular
Coq terms are not available. When a command argument contains a term, that
term is replaced by `_` at synterp time. In the following example, the synterp
program can see the name of the definition and the fact that a body was given,
but not the value of the body.

|*)


Elpi Command hello_synterp.
#[synterp] Elpi Accumulate lp:{{
  main [const-decl Name Body _] :- coq.say "synterp" Name ":=" Body.
}}.
Elpi Accumulate lp:{{
  main [const-decl Name Body _] :- coq.say "interp" Name ":=" Body.
}}.


Elpi hello_synterp Definition x := 2.

(*|

This simple command has no real synterp action, one could safely remove
the synterp code. On the contrary when a command performs actions affecting
the parser then it must come equipped with some synterp code performing
the corresponding actions.

|*)

Module Notations.
Notation "x '>>' y" := (x > y) (at level 40).
Definition w := 3.
End Notations.

Elpi Command import_module.
Elpi Accumulate lp:{{
  main [str M] :-
    coq.locate-module M MP,
    coq.env.import-module MP,
    coq.locate "w" (const GR),
    coq.env.const GR (some {{ 3 }}) _.
}}.


Fail Elpi import_module Notations. (* .fails .in .messages *)

(* oops, we forgot to declare code for the synterp phase. Here it is *)
#[synterp] Elpi Accumulate lp:{{
  main [str M] :-
    coq.locate-module M MP,
    coq.env.import-module MP.
}}.


Elpi import_module Notations.

(*|

Elpi reports a descriptive error message if actions affecting the parser are
not declared in the synterp code of the command.

.. mquote:: .s(Elpi import_module Notations).msg{*Interp*actions*must*match*synterp*actions*}
   :language: text

Thanks to the synterp code, Coq can parse the document without even looking
at the interp code.

Sometimes it is necessary to pass data from the synterp code to the interp one.
Passing data can be done in two ways. the former is by using the :e:`main-synterp`
and :e:`main-interp` entry points.

.. code:: elpi

    pred main-synterp i:list argument, o:any.
    pred main-interp i:list argument, i:any.

Unlike :e:`main` the former outputs a datum while the latter receives it
in input. In the following command we create a (empty) module with a random
name. Even if the name is random, the two phases need to agree on it, hence
we pass the name from one to the other.

|*)

Elpi Command mk_random_module.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [] M :-
    random.self_init,
    random.int 99 N,
    M is "Module" ^ {std.any->string N},
    coq.env.begin-module M none,
    coq.env.end-module _.
}}.
Elpi Accumulate lp:{{
  main-interp [] M :-
    coq.env.begin-module M none,
    coq.env.end-module MP,
    coq.say "The module is" MP.
}}.


Elpi mk_random_module.

(*|

If the only data to be passed to the interp phase is the list of
synterp actions, then a few APIs can come in handy.
The synterp phase has access to the API :builtin-synterp:`coq.synterp-actions`
that lists the actions performed so far. The interp phase can use
:lib:`coq.replay-synterp-action` and :builtin:`coq.next-synterp-action` to
replay an action or peek the next one to be performed.

An excerpt of the :type:`synterp-action`.

.. code:: elpi

    % Action executed during the parsing phase (aka synterp)
    kind synterp-action type.
    type begin-module id -> synterp-action.
    type end-module modpath -> synterp-action.

The following command creates a stack of modules and puts in there
the given definition. The synterp phase saves the actions when the top of the
stack is reached, and passes them to the interp phase that replays them before
putting a definition inside. Finally the interp phase replays all the missing
actions.

|*)

Elpi Command put_inside.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [int N, A] ActionsUpToNow :- N > 0, M is N - 1,
    coq.env.begin-module "Box" none,
    main-synterp [int M, A] ActionsUpToNow,
    coq.env.end-module _.
  main-synterp [int 0, _] ActionsUpToNow :-
    coq.synterp-actions ActionsUpToNow.
}}.
Elpi Accumulate lp:{{
  main-interp [int _, const-decl Name (some BO) _] Before :-
    std.forall Before coq.replay-synterp-action,
    coq.env.add-const Name BO _ _ _,
    replay-missing.
  pred replay-missing.
  replay-missing :-
    coq.replay-synterp-action {coq.next-synterp-action},
    replay-missing.
  replay-missing.
}}.



Elpi put_inside 4 Definition foo (n : nat) := n + 2.

Print Box.Box.Box.Box.foo.

(*|

This last example delegates to the synterp phase the creation of an arbitrary
complex module structure, a structure the interp phase does not need to be aware
of. The data passed to the interp phase is sufficient to replicate it without
too much effort.

Finally, as regular commands, data bases can be used to store a state which
is available at subsequent calls. Data bases used in the two phases live
in different name spaces, and are only available to the corresponding phase.
The `#[synterp]` attribute tells `Elpi Db` to create a data base for the
synterp phase. Here a simple command saving a state in the synterp phase.

|*)

#[synterp] Elpi Db counter.db lp:{{ pred tick. }}.

Elpi Command mk_next_module.
#[synterp] Elpi Accumulate Db counter.db.
#[synterp] Elpi Accumulate lp:{{
  main [] :-
    std.findall tick L,
    std.length L N,
    M is "NextModule" ^ {std.any->string N},
    coq.env.begin-module M none,
    coq.env.end-module _,
    coq.elpi.accumulate _ "counter.db" (clause _ _ tick).
}}.
Elpi Accumulate lp:{{
  main [] :- replay-missing.
  pred replay-missing.
  replay-missing :-
    coq.replay-synterp-action {coq.next-synterp-action},
    replay-missing.
  replay-missing.
}}.


Elpi mk_next_module.
Elpi mk_next_module.
Elpi mk_next_module.

Print Module NextModule2.

(*|

This is really the end, unless you want to learn more about writing
`tactics <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html>`_
in Elpi, in that case look at that tutorial ;-)

|*)
