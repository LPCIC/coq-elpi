HOAS for Rocq terms
=====================

.. seealso::
   An `Alectryon-rendered version
   <https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html>`_ of this
   tutorial, from before its migration to this manual, is also available.

This tutorial focuses on the integration of Elpi within Rocq, in particular
it describes how Rocq terms are exposed to Elpi programs and how Rocq APIs can
be called.

This tutorial assumes the reader is familiar with Elpi and HOAS; if it is not
the case, please take a look at the :doc:`elpi-lang` tutorial first.

.. contents::

HOAS for Gallina
--------------------

.. rocqtop:: none reset

   Set Warnings "-elpi.linear-variable".
   From elpi Require Import elpi.

   Elpi Command tutorial_HOAS.

The full syntax of Rocq terms can be found in
`coq-builtin.elpi <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin.elpi>`_
together with a detailed documentation of the encoding of contexts and the
APIs one can use to interact with Rocq. This tutorial, and the two more
that focus on commands and tactics, are a gentle introduction to all that.

We defer to later quotations and antiquotations: syntactic features that
let one write terms in Rocq's native syntax. Here we focus on the abstract
syntax tree of Rocq terms.

Constructor :e:`global`
~~~~~~~~~~~~~~~~~~~~~~~~~~

Let's start with the :type:`gref` data type (for global reference).

.. code-block:: elpi

   symb const : constant -> gref.
   symb indt : inductive -> gref.
   symb indc : constructor -> gref.

:type:`constant`, :type:`inductive` and :type:`constructor` are Rocq specific
data types that are opaque to Elpi. Still the :type:`gref` data type lets you
see what these names point to (a constant, and inductive type or a
constructor).

.. note:: keyword :e:`builtin symbol`

   Starting with Elpi 3.0 symbols like :e:`const`, :e:`indt` and
   :e:`indc` are declared using the keyword :e:`builtin symbol`,
   rather than :e:`type`, since they are coming from Rocq.

The :builtin:`coq.locate` API resolves a string to a :type:`gref`.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.locate "nat" GRnat,
     coq.locate "S" GRs,
     coq.locate "plus" GRplus

   }}.

The :e:`coq.env.*` family of APIs lets one access the
environment of well typed Rocq terms that have a global name.

.. rocqtop:: all

   Definition x := 2.

   Elpi Query lp:{{

     coq.locate "x" GR,

     % all global references have a type
     coq.env.typeof GR Ty,

     % destruct GR to obtain its constant part C
     GR = const C,

     % constants may have a body, do have a type
     coq.env.const C (some Bo) TyC

   }}.

An expression like :e:`indt «nat»` is not a Rocq term (or better a type) yet.

The :constructor:`global` term constructor turns a :type:`gref` into an
actual :type:`term`.

.. code-block:: elpi

   symb global : gref -> term.

Constructors :e:`app` and :e:`fun`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The :constructor:`app` term constructor takes a list of terms and builds
the (n-ary) application. The first term is the head, while the others
are the arguments.

For example :e:`app [global (indc «S»), global (indc «O»)]` is
the representation of ``1``.

.. code-block:: elpi

   symb app   : list term -> term.

Let's move to binders!

.. rocqtop:: all

   Definition f := fun x : nat => x.

   Elpi Query lp:{{

     coq.locate "f" (const C),
     coq.env.const C (some Bo) _

   }}.

The :constructor:`fun` constructor carries a pretty printing hint ```x```,
the type of the bound variable ``nat`` and a function describing the body:

.. code-block:: elpi

   symb fun  : name -> term -> (term -> term) -> term.

.. note:: :type:`name` is just for pretty printing: in spite of carrying
   a value in the Rocq world, it has no content in Elpi (like the unit type)

   Elpi terms of type :type:`name` are just identifiers
   written between ````` (backticks).

   .. rocqtop:: all

      Elpi Query lp:{{

        fun `foo` T B = fun `bar` T B    % names don't matter

      }}.

   API such as :builtin:`coq.name-suffix` lets one craft a family of
   names starting from one, eg ``coq.name-suffix `H` 1 N`` sets :e:`N`
   to ```H1```.

Constructors :e:`fix` and :e:`match`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The other binders :constructor:`prod` (Rocq's ``forall``, AKA ``Π``) and :constructor:`let` are similar,
so let's rather focus on :constructor:`fix` here.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.locate "plus" (const C),
     coq.env.const C (some Bo) _

   }}.

The :constructor:`fix` constructor carries a pretty printing hint,
the number of the recursive argument (starting at :e:`0`), the type
of the recursive function and finally the body where the recursive
call is represented via a bound variable

.. code-block:: elpi

   symb fix   : name -> int -> term -> (term -> term) -> term.

A :constructor:`match` constructor carries the term being inspected,
the return clause
and a list of branches. Each branch is a Rocq function expecting in input
the arguments of the corresponding constructor. The order follows the
order of the constructors in the inductive type declaration.

.. code-block:: elpi

   symb match : term -> term -> list term -> term.

The return clause is represented as a Rocq function expecting in input
the indexes of the inductive type, the inspected term and generating the
type of the branches.

.. rocqtop:: all

   Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
     match h as e in eq _ x return P 0 -> P x
     with eq_refl => fun (p : P 0) => p end.

   Elpi Query lp:{{

   coq.locate "m" (const C),
   coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
   coq.say "The return type of m is:" RT

   }}.

Constructor :e:`sort`
~~~~~~~~~~~~~~~~~~~~~~~~

The last term constructor worth discussing is :constructor:`sort`.

.. code-block:: elpi

   symb sort  : universe -> term.
   symb prop : universe.
   symb typ : univ -> universe.

The opaque type :type:`univ` is a universe level variable. Elpi holds a store of
constraints among these variables and provides APIs named :e:`coq.univ.*` to
impose constraints.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.sort.sup U U1,
     coq.say U "<" U1,
     % This constraint can't be allowed in the store!
     not(coq.sort.leq U1 U)

   }}.

.. note:: the user is not expected to declare universe constraints by hand

   The type checking primitives update the store of constraints
   automatically and put Rocq universe variables in place of Elpi's unification
   variables (:e:`U` and :e:`V` below).

Let's play a bit more with universe constraints using the
:builtin:`coq.typecheck` API:

.. rocqtop:: all

   Elpi Query lp:{{

     ID = (fun `x` (sort (typ U)) x\ x),
     A = (sort (typ U)), % the same U as before
     B = (sort (typ V)),
     coq.say "(id b) is:" (app [ID, B]),

     % error, since U : U is not valid
     coq.typecheck (app [ID, A]) T (error ErrMsg),
     coq.say "(id a) is illtyped:" ErrMsg,

     % ok, since V : U is possible
     coq.typecheck (app [ID, B]) T ok,

     % remark: U and V are now Rocq's univ with constraints
     coq.say "after typing (id b) is:" (app [ID, B]) ":" T,
     coq.univ.print

   }}.

The :stdtype:`diagnostic` data type is used by :builtin:`coq.typecheck` to
tell if the term is well typed. The constructor :e:`ok` signals success, while
:e:`error` carries an error message. In case of success universe constraints
are added to the store.

Quotations and Antiquotations
---------------------------------

Writing Gallina terms as we did so far is surely possible but very verbose
and unhandy. Elpi provides a system of quotations and antiquotations to
let one take advantage of the Rocq parser to write terms.

The antiquotation, from Rocq to Elpi, is written ``lp:{{ ... }}`` and we have
been using it since the beginning of the tutorial. The quotation from
Elpi to Rocq is written :e:`{{:coq ... }}` or also just :e:`{{ ... }}` since
the ``:coq`` is the default quotation (Rocq has no default quotation, hence you always need
to write ``lp:`` there).

.. rocqtop:: all

   Elpi Query lp:{{

     % the ":coq" flag is optional
     coq.say {{:coq 1 + 2 }} "=" {{ 1 + 2 }}

   }}.

Of course quotations can nest.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.locate "S" S,
     coq.say {{ 1 + lp:{{ app[global S, {{ 0 }} ]  }}   }}
   % elpi....  coq..     elpi...........  coq  elpi  coq

   }}.

One rule governs bound variables:

.. important::

   if a variable is bound in a language, Rocq or Elpi,
   then the variable is only visible in that language (not in the other one).

The following example is horrible but proves this point. In real code
you are encouraged to pick appropriate names for your variables, avoiding
gratuitous (visual) clashes.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:{{ x }} }})
   %                          e         c          c         e
   }}.

A commodity quotation without parentheses let's one quote identifiers
omitting the curly braces.
That is ``lp:{{ ident }}`` can be written just ``lp:ident``.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:x }})
   %                          e         c          c      e
   }}.

It is quite frequent to put Rocq variables in the scope of an Elpi
unification variable, and this can be done by simply writing
``lp:(X a b)`` which is a shorthand for ``lp:{{ X {{ a }} {{ b }} }}``.

.. warning:: writing ``lp:X a b`` (without parentheses) would result in a
   Rocq application, not an Elpi one

Let's play a bit with these shorthands:

.. rocqtop:: all

   Elpi Query lp:{{

     X = (x\y\ {{ lp:y + lp:x }}), % x and y live in Elpi

     coq.say {{ fun a b : nat => lp:(X a b) }} % a and b live in Rocq

   }}.

Another commodity quotation lets one access the coqlib
feature introduced in Rocq 8.10.

Rocqlib gives you an indirection between your code and the actual name
of constants.

.. rocqtop:: all

   Register Corelib.Init.Datatypes.nat as my.N.
   Register Corelib.Init.Logic.eq as my.eq.

   Elpi Query lp:{{

     coq.say {{ fun a b : lib:my.N => lib:@my.eq lib:my.N a b }}

   }}.

.. note:: The (optional) ``@`` in ``lib:@some.name`` disables implicit arguments.

The ``{{:gref .. }}`` quotation lets one build the gref data type, instead of the
term one. It supports ``lib:`` as well.

.. rocqtop:: all

   Elpi Query lp:{{

     coq.say {{:gref  nat  }},
     coq.say {{:gref  lib:my.N  }}.

   }}.

The last thing to keep in mind when using quotations is that implicit
arguments are inserted (according to the ``Arguments`` setting in Rocq)
but not synthesized automatically.

It is the job of the type checker or elaborator to synthesize them.
We shall see more on this in the section on `Holes (implicit arguments)`_.

.. rocqtop:: all

   Elpi Query lp:{{

     T = (fun `ax` {{nat}} a\ {{ fun b : nat => lp:a = b }}),
     coq.say "before:" T,
     coq.typecheck T _ ok,
     coq.say "after:" T

   }}.

The context
---------------

The context of Elpi (the hypothetical program made of rules loaded
via :e:`=>`) is taken into account by the Rocq APIs. In particular every time
a bound variable is crossed, the programmer *must* load in the context a
rule attaching to that variable a type. There are a few facilities to
do that, but let's first see what happens if one forgets it.

.. rocqtop:: all

   Fail Elpi Query lp:{{

     T = {{ fun x : nat => x + 1 }},
     coq.typecheck T _ ok,
     T = fun _ _ Bo,
     pi x\
       coq.typecheck (Bo x) _ _

   }}.

This fatal error says that :e:`x` in :e:`(Bo x)` is unknown to Rocq.
It is
a variable postulated in Elpi, but it's type, ``nat``, was lost. There
is nothing wrong per se in using :e:`pi x\ ` as we did if we don't call Rocq
APIs under it. But if we do, we have to record the type of :e:`x` somewhere.

In some sense Elpi's way of traversing a binder is similar to a Zipper.
The context of Elpi must record the part of the Zipper context that is
relevant for binders.

The two predicates :builtin:`decl` and :builtin:`def` are used
for that purpose:

.. code-block:: elpi

      func decl term -> name, term.       % Var Name Ty
      func def  term -> name, term, term. % Var Name Ty Bo

where :e:`def` is used to cross a :e:`let`.

.. rocqtop:: all

   Elpi Query lp:{{

     T = {{ fun x : nat => x + 1 }},
     coq.typecheck T _ ok,
     T = fun N Ty Bo,
     pi x\
       decl x N Ty ==>
         coq.typecheck (Bo x) _ ok

   }}.

In order to ease this task, Rocq-Elpi provides a few commodity macros such as
``@pi-decl``:

.. code-block:: elpi

       macro @pi-decl N T F :- pi x\ decl x N T ==> F x.

.. note:: the precedence of lambda abstraction :e:`x\ ` lets you write the
   following code without parentheses for :e:`F`.

.. rocqtop:: all

   Elpi Query lp:{{

     T = {{ fun x : nat => x + 1 }},
     coq.typecheck T _ ok,
     T =  fun N Ty Bo,
     @pi-decl N Ty x\
         coq.typecheck (Bo x) _ ok

   }}.

.. tip:: :e:`@pi-decl N Ty x\ ` takes arguments in the same order of :constructor:`fun` and
   :constructor:`prod`, while
   :e:`@pi-def N Ty Bo x\ ` takes arguments in the same order of :constructor:`let`.

Holes (implicit arguments)
------------------------------

An "Evar" (Rocq slang for existentially quantified meta variable) is
represented as a Elpi unification variable and a typing constraint.

.. rocqtop:: all
   :assert: (?=.*suspended on X0)(?=.*EVARS:.*\?X\d+==\[ \|- nat\])(?=.*Rocq-Elpi mapping:.*RAW:.*\?X\d+ <-> X0.*ELAB:.*\?X\d+ <-> X0)

   Elpi Query lp:{{

       T = {{ _ }},
       coq.say "raw T =" T,
       coq.sigma.print,
       coq.say "--------------------------------",
       coq.typecheck T {{ nat }} ok,
       coq.sigma.print

   }}.

Before the call to :builtin:`coq.typecheck`, :builtin:`coq.sigma.print`
prints nothing interesting, while after the call (see the output above) it
also prints a syntactic constraint stating that a hole is linked to a Rocq
evar and is expected to have type ``nat``.

Now the bijective mapping from Rocq evars to Elpi's unification variables is
not empty anymore, as the ``Rocq-Elpi mapping:`` line above shows.

Note that Rocq's evar identifiers are of the form ``?X<n>``, while the Elpi ones
have no leading ``?``. The ``EVARS:`` line of the output above shows that Rocq's
Evar map assigns that evar the type ``nat``.

The intuition is that Rocq's Evar map (AKA sigma or evd), which assigns
typing judgement to evars, is represented with Elpi constraints which carry
the same piece of info.

Naked Elpi unification variables, when passed to Rocq's API, are
automatically linked to a Rocq evar. We postpone the explanation of the
difference "raw" and "elab" unification variables to the chapter about
tactics, here the second copy of the hole variable in the evar constraint
plays no role.

Now, what about the typing context?

.. rocqtop:: all
   :assert: (?=.*suspended on X0)(?=.*EVARS:.*\?X\d+==\[x \|- nat\])(?=.*Rocq-Elpi mapping:.*RAW:.*\?X\d+ <-> X0.*ELAB:.*\?X\d+ <-> X0)

   Elpi Query lp:{{

     T = {{ fun x : nat => x + _ }},
     coq.say "raw T =" T,
     T = fun N Ty Bo,
     @pi-decl N Ty x\
         coq.typecheck (Bo x) {{ nat }} ok,
         coq.sigma.print.

   }}.

In the value of raw :e:`T` we can see that the hole in ``x + _``, which occurs under the
binder :e:`c0\ `, is represented by an Elpi unification variable :e:`X0 c0`, that
means that :e:`X0` sees :e:`c0` (:e:`c0` is in the scope of :e:`X0`).

The constraint is this time a bit more complex: as shown above, ``{...}`` is
the set of names (not necessarily minimized) used in the constraint, while
``?-`` separates the assumptions (the context) from the conclusion (the
suspended goal).

As shown by the mapping and evar-map lines of the output above, both Elpi's
constraint and Rocq's evar map record a context with a variable :e:`x` (of
type ``nat``) which is in the scope of the hole.

Unless one is writing a tactic, Elpi's constraints are just used to
represent the evar map. When a term is assigned to a variable
the corresponding constraint is dropped. When one is writing a tactic,
things are wired up so that assigning a term to an Elpi variable
representing an evar resumes a type checking goal to ensure the term has
the expected type.
We will explain this in detail in the tutorial about tactics.

Outside the pattern fragment
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This encoding of evars is such that the programmer does not need to care
much about them: no need to carry around an assignment/typing map like the
Evar map, no need to declare new variables there, etc. The programmer
can freely call Rocq API passing an Elpi term containing holes.

There is one limitation, though. The rest of this tutorial describes it
and introduces a few APIs and options to deal with it.

The limitation is that the automatic declaration and mapping
does not work in all situations. In particular it only works for Elpi
unification variables which are in the pattern fragment, which mean
that they are applied only to distinct names (bound variables).

This is the case for all the ``{{ _ }}`` one writes inside quotations, for
example, but it is not hard to craft a term outside this fragment.
In particular we can use Elpi's substitution (function application) to
put an arbitrary term in place of a bound variable.

.. rocqtop:: all
   :assert: Flexible term outside

   Fail Elpi Query lp:{{

     T = {{ fun x : nat => x + _ }},
     % remark the hole sees x
     T = fun N Ty Bo,
     % 1 is the offending term we put in place of x
     Bo1 = Bo {{ 1 }},
     % Bo1 is outside the pattern fragment
     coq.say "Bo1 (not in pattern fragment) =" Bo1,
     % boom
     coq.typecheck Bo1 {{ nat }} ok.

   }}.

This snippet fails hard, as shown above: the term :e:`Bo1` contains a term
outside the pattern fragment, the second argument of ``plus``, which is
obtained by replacing :e:`c0` with ``{{ 1 }}`` in :e:`X0 c0`.

While programming Rocq extensions in Elpi, it may happen that we want to
use a Rocq term as a syntax tree (with holes) and we need to apply
substitutions to it but we don't really care about the scope of holes.
We would like these holes to stay ``{{ _ }}`` (a fresh hole which sees the
entire context of bound variables). In some sense, we would like ``{{ _ }}``
to be a special dummy constant, to be turned into an actual hole on the
fly when needed.

This use case is perfectly legitimate and is supported by all APIs taking
terms in input thanks to the :macro:`@holes!` option.

.. rocqtop:: all

   Elpi Query lp:{{

     T = {{ fun x : nat => x + _ }},
     T = fun N Ty Bo,
     Bo1 = Bo {{ 1 }},
     coq.say "Bo1 before =" Bo1,
     % by loading this rule in the context, we set
     % the option for the APIs called under it
     (@holes! ==> coq.typecheck Bo1 {{ nat }} ok),
     coq.say "Bo1 after =" Bo1.

   }}.

Note that after the call to :builtin:`coq.typecheck`, the hole variable is
assigned a term where the offending argument has been pruned (discarded), as
shown by the ``Bo1 after`` line above.

.. note:: All APIs taking a term support the :macro:`@holes!` option.

In addition to the :macro:`@holes!` option, there is a class of APIs which can
deal with terms outside the pattern fragment. These APIs take in input a term
*skeleton*. A skeleton is not modified in place, as :builtin:`coq.typecheck`
does with its first argument, but is rather elaborated to a term related to it.

In some sense APIs taking a skeleton are more powerful, because they can
modify the structure of the term, eg. insert a coercions, but are less
precise, in the sense that the relation between the input and the output
terms is not straightforward (it's not unification).

.. rocqtop:: all

   Coercion nat2bool n := match n with O => false | _ => true end.
   Open Scope bool_scope.

   Elpi Query lp:{{

     T = {{ fun x : nat => x && _ }},
     T = fun N Ty Bo,
     Bo1 = Bo {{ 1 }},
     coq.elaborate-skeleton Bo1 {{ bool }} Bo2 ok

   }}.

Here :e:`Bo2` is obtained by taking :e:`Bo1`, considering all
unification variables as holes and all ``{{ Type }}`` levels as fresh
(the are none in this example), and running Rocq's elaborator on it.

The result is a term with a similar structure (skeleton), but a coercion
is inserted to make :e:`x` fit as a boolean value, and a fresh hole is
put in place of the term :e:`X0 (app [global (indc «S»), global (indc «O»)])`
which is left untouched.

Skeletons and their APIs are described in more details in the tutorial
on commands.

That is all for this tutorial. You can continue by reading the tutorial
about :doc:`coq-commands` or the one about :doc:`coq-tactics`.
