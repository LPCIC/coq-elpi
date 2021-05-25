From elpi Require Import elpi.
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

(** ----------------------- ----------------------- -----------------------

   This tutorial focuses on the integration of Elpi within Coq, in particular
   it describes how Coq terms are exposed to Elpi programs and how Coq APIs can
   be called.

   This tutorial assumes the reader is familiar with Elpi and HOAS; if it is not
   the case, please take a look at this other tutorial first:
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_elpi_lang.v

   Contents:
   - HOAS for Gallina
   - Quotations and Antiquotations
   - The context
   - Holes (implicit arguments)

*)

Elpi Command tutorial_HOAS. (* ignore this *)


(** ----------------------- HOAS for Gallina ----------------------------- *)

(**
     The full syntax of Coq terms can be found here

        https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

     We defer to later quotations and antiquotations: syntactic features that
     let one write terms in Coq's native syntax. Here we focus on the abstract
     syntax tree.

     Let's start with the "gref" data type and the "global" term
     constructor.

     The "coq.locate" builtin resolves a name to a global rerence ("gref").

      type const constant -> gref.
      type indt inductive -> gref.
      type indc constructor -> gref.

     "constant", "inductive" and "constructor" are Coq specific data
     types that are opaque to Elpi. Still the "gref" data type lets you
     see what these names point to (a constant, and inductive type or a
     constructor).
*)

Elpi Query lp:{{

  coq.locate "nat" GRnat,   coq.say "nat is:" GRnat,
  coq.locate "S" GRs,       coq.say "S is:" GRs,
  coq.locate "plus" GRplus, coq.say "plus is:" GRplus.

}}.

(**
   The "coq.env.*" family of built-in predicates lets one access the
   environment of well typed Coq terms that have a global name.
   *)

Definition x := 2.

Elpi Query lp:{{

  coq.locate "x" GR,
  coq.env.typeof GR Ty, % all global references have a type
  coq.say "The type of x is:" Ty,

  GR = const C, % destruct GR to obtain its constant part C
  coq.env.const C (some Bo) TyC, % constans may have a body, do have a type
  coq.say "The body of x is:" Bo

}}.

(**
    Remark: "indt «nat»" is not a term (or better a type).
    The "global" term constructor turns a "gref" into an actual term.

    type global gref -> term.

    Remark: the "app" term constructor is taking a list of terms and building
    the application. "app [global (indc «S»), global (indc «O»)]" is
    the representation of 1.

    type app   list term -> term.

    Let's move to binders!
*)

Definition f := fun x : nat => x.

Elpi Query lp:{{

  coq.locate "f" (const C),
  coq.env.const C (some Bo) _,
  coq.say "The body of f is:" Bo

}}.

(**
   The "fun" constructor carries a pretty printing hint "`x`", the type
   of the bound variable "nat" and a function describing the body:

     type fun  name -> term -> (term -> term) -> term.

   Remark: name is just for pretty printing, in spite of carrying
   a value in the Coq world, it has no content in Elpi (like the unit type).
   Elpi terms of type name are just identifiers written between "`" (backticks).
   
   Remark: API such as coq.name-suffix lets one craft a family of names starting
   from one, eg "coq.name-suffix `H` 1 N" sets N to `H1`
*)

Elpi Query lp:{{
  
  fun `foo` T B = fun `bar` T B
  
}}.

(**
   The other binders "prod" (Coq's "forall", AKA "Π") and "let" are similar,
   so let's rather focus on "fix" here.
*)

Elpi Query lp:{{

  coq.locate "plus" (const C),
  coq.env.const C (some Bo) _,
  coq.say "The body of plus is:" Bo

}}.

Check match 3 as w in nat return bool with 0 => true | S _ => false end.

(**
   The "fix" constructor carries a pretty printing hint, the number of the
   recursive argument (starting at 0), the type and finally the body where the
   recursive call is represented via a bound variable

     type fix   name -> int -> term -> (term -> term) -> term.

   A "match" constructor carries the term being inspected, the return clause
   and a list of branches. Each branch is a Coq function expecting in input
   the arguments of the corresponding constructor. The order follows the
   order of the constructors in the inductive type declaration.

     type match term -> term -> list term -> term.

   The return clause is represented as a Coq function expecting in input
   the indexes of the inductive type, the inspected term and generating the
   type of the branches.
*)

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
  match h as e in eq _ x return P 0 -> P x
  with eq_refl => fun (p : P 0) => p end.

Elpi Query lp:{{

    coq.locate "m" (const C),
    coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
    coq.say "The return type of m is:" RT

}}.


(**
   The last term constructor worth discussing is "sort".

   type sort  universe -> term.

   type prop universe.
   type typ univ -> universe.

   The opaque "univ" is a universe level variable. Elpi holds a store of
   constraints among these variables and provides built-in predicates
   named "coq.univ.*" to impose constraints.
*)

Elpi Query lp:{{

  coq.univ.sup U U1,
  coq.say U "<" U1,
  not(coq.univ.leq U1 U) % This constraint can't be allowed in the store!

}}.

(**
    Note that the user is not required to declare universe constraints by hand,
    since the type checking primitives update the store of constraints
    automatically and put Coq universe variables in place of Elpi's unification
    variables (U and V below).
*)

Elpi Query lp:{{

  ID = (fun `x` (sort (typ U)) x\ x),
  A = (sort (typ U)), % the same U as before
  B = (sort (typ V)),
  coq.say "(id b) is:" (app [ID, B]),
  coq.typecheck (app [ID, A]) T (error ErrMsg), % since U : U is not valid
  coq.say ErrMsg,
  coq.typecheck (app [ID, B]) T ok,        % since V : U is possible
  coq.say "(id b) is now:" (app [ID, B]) ":" T, % remark: U and V are now Coq's
  coq.univ.print                                % univ with constraints

}}.

(** --------------- Quotations and Antiquotations ------------------------- *)

(**
   Writing Gallina terms as we did so far is surely possible but very verbose
   and unhandy. Elpi provides a system of quotations and antiquotations to
   let one take advantage of the Coq parser to write terms.

   The antiquotation, from Coq to Elpi, is written lp:{{ .. }} and we have
   been using it since the beginning of the tutorial. The quotation from
   Elpi to Coq is written {{:coq .. }} or also just {{ .. }} since the ":coq" is
   the default quotation. (Coq has no default quotation, hence you always need
   to write "lp:" there).
*)

Elpi Query lp:{{

  coq.say {{:coq 1 + 2 }} "=" {{ 1 + 2 }}

}}.

(** Of course quotations can nest. *)

Elpi Query lp:{{

  coq.locate "S" S,
  coq.say {{ 1 + lp:{{ app[global S, {{ 0 }} ]  }}   }}
% elpi....  coq..     epi............  coq  elpi  coq
}}.

(**
   One rule governs bound variables:

     if a variable is bound in a language, Coq or Elpi,
     then the variable is only visible in that language (not in the other one).

   The following example is horrible but proves this point. In real code
   you are encouraged to pick appropriate names for your variables, avoiding
   gratuitous (visual) clashes.
*)

Elpi Query lp:{{

  coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:{{ x }} }})
%                          e         c          c         e
}}.

(**
   A commodity quotation without parentheses let's one quote identifiers
   omitting the curly braces.
   That is "lp:{{ <ident> }}" can be written just "lp:<ident>".
*)


Elpi Query lp:{{

  coq.say (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:x }})
%                          e         c          c      e
}}.

(**
   It is quite frequent to put Coq variables in the scope of an Elpi
   unification variable, and this can be done by sinmply writing
   "lp:(X a b)" which is a shorhand for "lp:{{ X {{ a }} {{ b }} }}".

   Note that writing "lp:X a b" (without parentheses) would result in a
   Coq application, not an Elpi one. *)

Elpi Query lp:{{

  X = (x\y\ {{ lp:y + lp:x }}),
  coq.say {{ fun a b : nat => lp:(X a b) }}

}}.

(**
    Another commodity quotation lets one access the "coqlib"
    feature introduced in Coq 8.10.

    Coqlib gives you an indirection between your code and the actual name
    of constants.

    Remark: the optional "@" to disable implicits. *)

Register Coq.Init.Datatypes.nat as my.N.
Register Coq.Init.Logic.eq as my.eq.

Elpi Query lp:{{

  coq.say {{ fun a b : lib:my.N => lib:@my.eq lib:my.N a b }}

}}.


(**
    The "{{:gref .. }}" quotation lets one the gref data type, instead of the
    term one. It supports "lib:" as well. *)

Elpi Query lp:{{
 
  coq.say {{:gref  nat  }},
  coq.say {{:gref  lib:my.N  }}.

}}.

(**
    The last thing to keep in mind when using quotations is that implicit
    arguments are inserted (according to the Arguments setting in Coq)
    but not synthesized automatically.
    
    It is the job of the type checker or elaborator to synthesize them.
    We shall see more on this in the section on Holes.
*)

Elpi Query lp:{{

  T = (fun `ax` {{nat}} a\ {{ fun b : nat => lp:a = b }}),
  coq.say "before:" T,
  % this is the standard Coq typechecker (but you may write your own ;-)
  coq.typecheck T _ ok,
  coq.say "after:" T.

}}.

(** ----------------------- HOAS for Gallina ----------------------------- *)


(**
    The context of Elpi (the hypothetical program made of clauses loaded
    via "=>") is taken into account by the Coq APIs. In particular every time
    a bound variable is crossed, the programmer must load in the context a
    clause attaching to that variable a type. There are a few facilities to
    do that, but let's first see what happens if one forgets it.
*)

Fail Elpi Query lp:{{

  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T = fun _ _ Bo,
  pi x\
    coq.typecheck (Bo x) _ _.

}}. (* Error:

Bound variable c0 not found in the Coq context:
Mapping from DBL:
  

Named:
  
Rel:
  
Did you forget to load some hypotheses with => ?

*)

(** 
    This fatal error says that "x" in "(Bo x)" is unknown to Coq. It is
    a variable postulated in Elpi, but it's type, "nat", was lost. There
    is nothing wrong per se in using "pi x\" as we did if we don't call Coq
    APIs under it. But if we do, we have to record the type of "x" somewhere.

    In some sense Elpi's way of traversing a binder is similar to a Zipper.
    The context of Elpi must record the part of the Zipper context that is
    relevant for binders.

    The following two predicates are used for that purpose:

    pred decl i:term, o:name, o:term. % Var Name Ty
    pred def  i:term, o:name, o:term, o:term. % Var Name Ty Bo
       
    where "def" is used to cross "let-in"
*)

Elpi Query lp:{{

  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T = fun N Ty Bo,
  pi x\
    decl x N Ty =>
      coq.typecheck (Bo x) _ ok.

}}.

(**
     In order to ease this task, Coq-Elpi provides a few commodity macros in:

       https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

     For example:

       macro @pi-decl N T F :- pi x\ decl x N T => F x.

     Remeber the precedence of lambda abstraction "x\" which lets you write the
     following without parentheses for F.
*)

Elpi Query lp:{{

  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T = fun N Ty Bo,
  @pi-decl N Ty x\
      coq.typecheck (Bo x) _ ok.

}}.

(** -------------------- Holes (implicit arguments) ----------------------- *)

(**
     An "Evar" (Coq slang for existentially quantified meta variable) is
     reprsented as a Elpi unification variable and a typing constraint. *)

Elpi Query lp:{{

    T = {{ _ }},
    coq.say "raw T =" T,
    coq.sigma.print,
    coq.say "--------------------------------------------------------",
    coq.typecheck T {{ nat }} ok,
    coq.sigma.print
    
}}.
    
(**
     Before the call to coq.typecheck, Elpi just prints:

       raw T = X0

     After the call it also prints the following syntactic constraint:

       evar X0 (global (indt «nat»)) X0  /* suspended on X0 */

     which indicates that the hole X0 is expected to have type nat.

     The API coq.sigma.print also dumps some debugging info: Coq's "evar_map"
     and a bijective mapping from Coq evars to Elpi's unification variables.

     Before the call the mapping is empty. After the call it prints:

        Coq-Elpi mapping:
        RAW:
        ?X11 <-> X0
        ELAB:
        ?X11 <-> X0

     Note that Coq's evar identifiers are of the form ?X<n>, while the Elpi ones
     have no leading "?". The Coq "evar map" says that ?X11 has type nat:

        EVARS:
        ?X11==[ |- nat] (internal placeholder) {?e0}

     The intuition is that Coq's evar map (AKA sigma or evd), which assigns
     typing judgement to evars, is represented with Elpi consaints which carry
     the same piece of info.

     Naked Elpi unification variables, when passed to Coq's API, are
     automatically linked to a Coq evar. We postpone the explanation of the
     difference "raw" and "elab" unification variables to the chapter about
     tactics, here the second copy of X0 in the evar constraint plays no role.

     Now, what about the typing context?
*)

Elpi Query lp:{{

  T = {{ fun x : nat => x + _ }},
  coq.say "raw T =" T,
  T = fun N Ty Bo,
  @pi-decl N Ty x\
      coq.typecheck (Bo x) {{ nat }} ok,
      coq.sigma.print.

}}.

(**
    Here we can see that the hole in "x + _", which occurs under the
    binder "c0\", is represented by an Elpi unification variable "X0 c0", that
    means that X0 sees c0 (c0 is in the scope of X0).
 
     raw T = 
       fun `x` (global (indt «nat»)) c0 \
         app [global (const «Nat.add»), c0, X0 c0]
 
    This time the constraint is
 
      {c0 c1} :
        decl c1 `x` (global (indt «nat»)) ?-
          evar (X0 c1) (global (indt «nat»)) (X0 c1)  /* suspended on X0 */
 
    Here {...} is the set of names (not necessarily minimized) used in the
    constraint, while ?- separates the assumptions from the conclusion.
 
    The mapping between Coq and Elpi is ?X13 <-> X0, where
 
      EVARS:
        ?X13==[x |- nat] (internal placeholder) {?e0}
 
    As expected both Elpi's constraint and Coq's evar map record a context
    for a variable "x" (of type nat) which is in the scope of the hole.
 
    Unless one is writing a tactic, Elpi's constraints are just used to
    represent the evar map entry of evars. When a variable is assigned to a
    term the corresponding constraint is dropped. When one is writing a tactic,
    things are wired up so that assigning a term to an Elpi variable
    representing an evar resumes a type checking goal to ensure the term has
    the expected type.
    We will explain this in detail in the chapter about tactics.

*)

(**
    This encoding of evars is such that the programmer does not need to care
    much about them: no need to carry around an assignment/typing map like the
    evar map, no need to declared new variables there, etc. The programmer
    can freely call Coq API passing an Elpi term containing holes.

    There is one limitation, though. The rest of this chapter describes it
    and introduces a few APIs and options to deal with it.

    The limitation is that the automatic declaration and mapping
    does not work in all situations. In particular it only works for Elpi
    unification variables which are in the pattern fragment, which mean
    that they are applied only to distinct names (bound variables).

    This is the case for all the {{ _ }} one uses inside quotations, for
    example, but it is not hard to craft a term outside this fragment.
    In particular we can use Elpi's substitution (function application) to
    put an arbitrary term in place of a bound variable.

*) 

Fail Elpi Query lp:{{

  T = {{ fun x : nat => x + _ }},
  T = fun N Ty Bo,      % remark the hole sees x
  Bo1 = Bo {{ 1 }},     % 1 is the offending term we put in place of x
  coq.say "Bo1 =" Bo1,  % Bo1 is outside the pattern fragment
  coq.typecheck Bo1 {{ nat }} ok. % boom

}}.

(**
    This snippet fails hard, with the following message:

        Flexible term outside pattern fragment:
        X0 (app [global (indc «S»), global (indc «O»)])

    Indeed Bo1

      app
      [global (const «Nat.add»), 
        app [global (indc «S»), global (indc «O»)], 
        X0 (app [global (indc «S»), global (indc «O»)])]

    contains a term outside the pattern fragment, the second argument of plus,
    which is obtained by replacing c0 with {{ 1 }} in "X0 c0".

    While programming Coq extensions in Elpi, it may happen that we want use a
    Coq term as a syntax tree (with holes) and we need to apply substitutions to
    it but we don't really care about the scope of holes, we would like these
    holes to stay {{ _ }} (a fresh hole which sees the entire context of bound
    variables). In some sense, we would like {{ _ }} to be a special dummy
    constant, to be turned into an actual hole on the fly when needed.

    This use case is perfectly legitimate and is supported by all APIs taking
    terms in input thanks to the @holes! option.
    
*)

Elpi Query lp:{{

  T = {{ fun x : nat => x + _ }},
  T = fun N Ty Bo,
  Bo1 = Bo {{ 1 }},
  coq.say "Bo1 =" Bo1,
  @holes! => coq.typecheck Bo1 {{ nat }} ok,
  coq.say "Bo1 =" Bo1.

}}.

(**

    Note that after the call to coq.typecheck X0 is assigned with _\X1, that is,
    the offending argument has been pruned.
    
      Bo1 = app
        [global (const «Nat.add»), 
           app [global (indc «S»), global (indc «O»)],
           X1]

    All APIs taking a term support this option which is documented in details
    in https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

    In addition to @holes! option, there is a class of API which can deal with
    terms outside the pattern fragment are the ones taking in input a term
    skeleton. A skeleton is not modified in place, as coq.typecheck does with
    its first input, but is rather elaborated to a term related to it.
    In some sense APIs taking a skeleton are more powerful, because the can
    modify the structure of the term, eg. insert a coercions, but are less
    precise, in the sense that the relation between the input and the output
    terms is not straightforward (it's not unification).

*)

Coercion nat2bool n := match n with O => false | _ => true end.
Open Scope bool_scope.

Elpi Query lp:{{

  T = {{ fun x : nat => x && _ }},
  T = fun N Ty Bo,
  Bo1 = Bo {{ 1 }},
  coq.elaborate-skeleton Bo1 {{ bool }} Bo2 ok,
  coq.say "Bo1 =" Bo1, % we print it after the call, to see if it changed
  coq.say "Bo2 =" Bo2.

}}.

(**
    Here Bo2 is obtained by taking Bo1, considering all unification variables 
    as holes and all type levels as fresh (the are none in this example), and
    running Coq's elaborator on it:
    
      Bo2 = 
        app [global (const «andb»), 
             app [global (const «nat2bool»),
                  app [global (indc «S»), global (indc «O»)]],
             X1]

    The result is a term with a similar structure (skeleton), but a coercion
    is inserted to make "x" fit as a boolean value, and a fresh hole X1 is
    put in place of the term "X0 (app [global (indc «S»), global (indc «O»)])"
    which is left untouched.

    Skeletons and their APIs are described in more details in the chapter
    on commands.
*)