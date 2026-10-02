Polishing a command
========================

.. seealso::
   An `Alectryon-rendered version
   <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html>`_ of
   this tutorial (together with :doc:`coq-commands`), from before its
   migration to this manual, is also available.

This page continues :doc:`coq-commands`, covering attributes, extending the
command grammar, error reporting, and the separation between parsing and
execution.

.. contents::

.. rocqtop:: none reset

   Set Warnings "-elpi.linear-variable".
   From elpi Require Import elpi.

The details do make the difference, some times.

Extending the command grammar
---------------------------------

Elpi programs can be exported as regular Rocq commands, so that the
final user does not need to type ``Elpi`` to invoke them.

.. rocqtop:: all

   Elpi Command Say.
   Elpi Accumulate lp:{{ main [str S] :- coq.say S. }}.

   Elpi Export Say. (* extend the Rocq command grammar *)

   Say "That is all folks!".

Not yet...

Rocq offers no equivalent of ``Tactic Notation`` for commands.
Still Elpi commands accept any symbol or keyword as strings.
It is up to the programmer to catch and report parse errors.

.. rocqtop:: all

   Elpi Command Go.
   Elpi Accumulate lp:{{
     main [str Src, str "=>", str Tgt, str "/", str F] :- !,
       coq.say "going from" Src "to" Tgt "via" F.
     main _ :-
       coq.error "Parse error! Use: go <from> => <to> / <via>".
   }}.

   Elpi Export Go.

   Go source => target / plane.
   Fail Go nowhere.

Attributes
-------------

Elpi programs can be prefixed with attributes, like ``#[local]``.
Attributes are not passed as arguments but rather as a rule in the context,
a bit like the option :e:`@holes!` we have seen before.

.. rocqtop:: all

   Elpi Command attr.
   Elpi Accumulate lp:{{

     main _ :-
       attributes A, % we fetch the list of attributes from the context
       coq.say A.

   }}.
   Elpi Export attr.
   #[this, more(stuff="33")] attr.

The first attribute, :e:`elpi.loc` is always present and corresponds to the
location in the source file of the command. Then we find an attribute for
:e:`"this"` holding the empty string and an attribute for :e:`"more.stuff"` holding
the string :e:`"33"`.

Attributes are usually validated (parsed) and turned into regular options
using :lib-common:`coq.parse-attributes` and a description of their types using
the :libtype-common:`attribute-type` data type:

.. rocqtop:: all

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
       (Opts =!=> some-code).

   }}.
   Elpi Export parse_attr.
   #[this, more(stuff="33")] parse_attr.
   Fail #[unknown] parse_attr.

Note that :e:`get-option` links a string with a datum of type :e:`any`, which means
no type checking is performed on it. It is recommended to wrap calls to
get-option into other predicates typed in a more precise way. Eg:

.. code-block:: elpi

   pred get-my-option -> int.
   get-my-option I :- get-option "my-option-name" I.

Reporting errors
--------------------

Good Elpi programs should fail reporting intelligible error messages,
as the previous one.

.. rocqtop:: all
   :assert: inconvenience

   Elpi Command bad.
   Elpi Accumulate lp:{{ main []. }}.

   Elpi Export bad.

   Fail bad 1.

If they just fail, as shown above, they produce a rather generic error
message. You should use the :builtin:`coq.error` API or the :stdlib:`assert!` one
to abort a program. There is a dedicated :builtin:`coq.ltac.fail` API to abort
tactics.

Warnings can be reported using the :builtin:`coq.warning` which lets you
pick a name and category. In turn these can be used to disable or make fatal
your warnings (as any other Rocq warning).

Parsing and Execution
-------------------------

Since version 8.18 Rocq has separate parsing and execution phases,
respectively called synterp and interp.

Since Rocq has an extensible grammar the parsing phase is not entirely
performed by the parser: after parsing one sentence Rocq evaluates its
synterp action. The synterp actions of a command like ``Import A.`` are
the subset of its effect which affect parsing, like enabling a notation.
Later, during the execution phase, Rocq evaluates its
interp actions, which include effects like putting lemma in scope or
enabling type class instances etc. Synterp actions are quick, if only because
they don't really manipulate Rocq terms, hence no type checking and the like.

Being able to parse an entire document quickly
is important for developing reactive
user interfaces, but requires some extra work when defining new commands,
in particular to identify their synterp.
Each command defined with Rocq-Elpi is split into two programs,
one running during the parsing phase and the other one during the execution
phase. Each API that affects the parser, i.e. APIs dealing with modules
and sections like begin/end-module or import/export, is available to both the
synterp and the interp program under the same name, but its actual effect is
limited to what concerns the current phase. Hence all these APIs have to be
called at *both* synterp and interp time and *in the same order*.

At synterp time the data types and the APIs are restricted, in particular
Rocq terms are not available. When a command argument contains a term, that
term is replaced by ``_`` at synterp time. In the following example, the synterp
program can see the name of the definition and the fact that a body was given,
but not the value of the body.

.. rocqtop:: all

   Elpi Command hello_synterp.
   #[synterp] Elpi Accumulate lp:{{
     main [const-decl Name Body _] :- coq.say "synterp" Name ":=" Body.
   }}.
   Elpi Accumulate lp:{{
     main [const-decl Name Body _] :- coq.say "interp" Name ":=" Body.
   }}.

   Elpi hello_synterp Definition x := 2.

This simple command has no real synterp action, one could safely remove
the synterp code. On the contrary when a command performs actions affecting
the parser then it must come equipped with some synterp code performing
the corresponding actions.

.. rocqtop:: all

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

   Fail Elpi import_module Notations.

Elpi reports a descriptive error message if actions affecting the parser are
not declared in the synterp code of the command.

Thanks to the synterp code below, Rocq can parse the document without even looking
at the interp code.

.. rocqtop:: all

   (* oops, we forgot to declare code for the synterp phase. Here it is *)
   #[synterp] Elpi Accumulate lp:{{
     main [str M] :-
       coq.locate-module M MP,
       coq.env.import-module MP.
   }}.

Sometimes it is necessary to pass data from the synterp code to the interp one.
Passing data can be done in two ways. the former is by using the :e:`main-synterp`
and :e:`main-interp` entry points.

.. code-block:: elpi

    pred main-synterp list argument -> any.
    pred main-interp list argument, any.

Unlike :e:`main` the former outputs a datum while the latter receives it
in input. In the following command we create a (empty) module with a random
name. Even if the name is random, the two phases need to agree on it, hence
we pass the name from one to the other.

.. rocqtop:: all

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

If the only data to be passed to the interp phase is the list of
synterp actions, then a few APIs can come in handy.
The synterp phase has access to the API :builtin-synterp:`coq.synterp-actions`
that lists the actions performed so far. The interp phase can use
:lib:`coq.replay-synterp-action` and :builtin:`coq.next-synterp-action` to
replay an action or peek the next one to be performed.

An excerpt of the :type:`synterp-action`.

.. code-block:: elpi

    % Action executed during the parsing phase (aka synterp)
    data synterp-action.
    symb begin-module : id -> synterp-action.
    symb end-module : modpath -> synterp-action.

The following command creates a stack of modules and puts in there
the given definition. The synterp phase saves the actions when the top of the
stack is reached, and passes them to the interp phase that replays them before
putting a definition inside. Finally the interp phase replays all the missing
actions.

.. rocqtop:: all

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

This last example delegates to the synterp phase the creation of an arbitrary
complex module structure, a structure the interp phase does not need to be aware
of. The data passed to the interp phase is sufficient to replicate it without
too much effort.

Finally, as regular commands, data bases can be used to store a state which
is available at subsequent calls. Data bases used in the two phases live
in different name spaces, and are only available to the corresponding phase.
The ``#[synterp]`` attribute tells ``Elpi Db`` to create a data base for the
synterp phase. Here a simple command saving a state in the synterp phase.

.. rocqtop:: all

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

This is really the end, unless you want to learn more about writing
tactics in Elpi, in that case look at :doc:`coq-tactics` ;-)
