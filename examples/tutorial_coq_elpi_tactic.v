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

   This tutorial focuses on the implementation of Coq tactics.

   This tutorial assumes the reader is familiar with Elpi and the HOAS
   representation of Coq terms; if it is not the case, please take a look at
   this other tutorials first:
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_elpi_lang.v
     https://github.com/LPCIC/coq-elpi/blob/master/examples/tutorial_coq_elpi_HOAS.v

   - Defining tactics
   - Arguments and Tactic Notation
   - Examples: assumption and set
   - The proof state
   - msolve and tactic composition
   - Tactic in terms

*)

(** ------------------------- Defining tactics ---------------------------- *)

(**
   In Coq a proof is just a term, and an incomplete proof is just a term
   with holes standing for the open goals.

  When a proof starts there is just one hole (one goal) and its type
  is the statement one wants to prove. Then proof construction makes
  progress by instantiation: a term possibly containing holes is
  grafted to the hole corresponding to the current goal. What a tactic
  does behind the scenes is to synthesize this partial term.

  Let's define a simple tactic that prints the current goal.

*)

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type,
    coq.say "Proof state:"

}}.
Elpi Typecheck.

(*

  The tactic declaration is made of 3 parts.
     
  The first one "Elpi Tactic show." sets the current program to "show".
  Since it is declared as a "Tactic" some code is loaded automatically:
  - built-in predicates (eg "coq.say") and data types (eg Coq terms)
    https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
  - some utilities, like "copy" or "whd1"
    https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi
  
  
  The second one "Elpi Accumulate ..." loads some extra code.
  The "Elpi Accumulate ..." family of commands lets one accumulate code
  taken from:
  - verbatim text "Elpi Accumulate lp:{{ <code> }}"
  - source files "Elpi Accumulate File <path>"
  - data bases (Db) "Elpi Accumulate Db <name>"
  Accumulating code via inline text of file is equivalent, the AST of code
  is stored in the .vo file (the external file does not need to be installed).
  We invite the reader to look up the description of data bases in the tutorial
  about commands.
  
  Once all the code is accumulated "Elpi Typecheck" verifies that the
  code does not contain the most frequent kind of mistakes. This command
  considers some mistakes minor and only warns about them. You can
  pass "-w +elpi.typecheck" to coqc to turn these warnings into errors.
  
  The entry point for tactics is called "solve" which maps a goal
  into a list of sealed-goal (representing subgoals).
  
  Tactics written in Elpi can be invoked via the "elpi" tactic.
*)

Lemma tutorial x y  : x + 1 = y.
elpi show.
Abort.

(**

  In the Elpi code up there "Proof" is the hole for the current goal,
  "Type" the statement to be proved and "Ctx" the proof context. Since we
  don't assign "Proof" the tactic makes no progess. Elpi prints something
  like this:

    Goal:
    [decl c0 `x` (global (indt «nat»)), decl c1 `y` (global (indt «nat»))] 
    |- X0 c0 c1 : 
       app [global (indt «eq»), global (indt «nat»), 
            app [global (const «Nat.add»),
                 c0, app [global (indc «S»), global (indc «O»)]],
            c1]

  The first line is the proof context:
  proof variables are bound Elpi variables (here "c0" and "c1"), the context is
  a list of predicates holding on them (their type in Coq). For example:

    decl c0 `x` (global (indt «nat»))

  asserts that "c0" (pretty printed as "`x`") has type "nat".

  Then we see that the value of "Proof" is "X0 c0 c1". This means that the
  proof of the current goal is represented by Elpi's variable "X0" and that
  the variable has "c0" and "c1" in scope (the proof can use them).

  Finally we see find the type of the goal "x + 1 = y".

  The _Trigger component, which we did not print, is a variable that, when
  assigned, trigger the elaboration of its value against the type of the goal
  and obtains a value for Proof this way.

  Keping in mind that the solve predicate relates one goal to a list of
  subgoals, we implemet our first tactic which blindly tries to solve the Goal.

*)

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{0}}.
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{I}}.
}}.
Elpi Typecheck.

Lemma test_blind : True * nat.
Proof.
split.
- elpi blind.
- elpi blind.
Show Proof.
Qed.

(**

   Since the assignment of a term to Trigger triggers its elaboration against
   the expected type (the goal statement), assigning the wrong proof term
   results in a failure which in turn results in the other clause being tried.

   Assigning Proof directly is "unsound" in the sense that no automatic check
   is performed.

*)

Elpi Tactic blind_bad.
Elpi Accumulate lp:{{
  solve (goal _ _ _ Proof _) [] :- Proof = {{0}}.
  solve (goal _ _ _ Proof _) [] :- Proof = {{I}}.
}}.
Elpi Typecheck.

Lemma test_blind_bad : True * nat.
Proof.
split.
- elpi blind_bad.
- elpi blind_bad.
Show Proof.
Fail Qed.
Abort.


(**

   For now, this is all about the low level mechanics of tactics which is
   developed further in the section "The proof state".
   
   We now focus on how to better integrate tactics written in Elpi with Ltac.

   For this simple tactic the list of subgoals is easy to write, snice it is
   empty, but in general one should collect all the holes in the value of
   Proof (the checked proof term) and build goals out of them.

   There is a family of APIs named after refine in
     https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi
   which does this job for you.

   In general a tactic builds a (possibly partial) term and calls refine on it.
   Let's rewrite the blind tactic using this schema.

*)


Elpi Tactic blind2.
Elpi Accumulate lp:{{
  solve G GL :- refine {{0}} G GL.
  solve G GL :- refine {{I}} G GL.
}}.
Elpi Typecheck.

Lemma test_blind2 : True * nat.
Proof.
split.
- elpi blind2.
- elpi blind2.
Qed.

(**

   Elpi's equality on ground (evar free) Coq terms corresponds to
   alpha equivalence.
   Moreover the head of a clause for the solve predicate is matched against the
   goal: this operation cannot assign unification variables in the goal, only
   variables in the clause's head.
   
   As a consequence the following clause for "solve" only triggers when
   the statement features an explicit conjunction.
*)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    refine {{ conj _ _ }} G GL.
  solve _ _ :-
    % This signals a failure in the Ltac model. A failure in Elpi, that
    % is no more cluases to try, is a fatal error that cannot be catch
    % by Ltac combinators like repeat.
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split. (* The failure is catched by Ltac's repeat *)
(* Remark that the last goal is left untouched, since it did not match the
   pattern {{ _ /\ _ }}. *)
all: elpi blind.
Show Proof.
Qed.

(**
   The tactic split succeeds twice, stopping on the two identical goals True and
   the one which is an evar of type Prop.

   We then invoke blind on all goals. In the third case the type checking
   constraint triggered by assigning {{0}} to Proof fails because
   its type {{nat}} is not of sort Prop, so it backtracks and picks {{I}}.

   Another common way to build an Elpi tactic is to synthesize a term and
   then call some Ltac piece of code finishing the work.
*)

Ltac helper_split2 t := apply t.

Elpi Tactic split2.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    coq.ltac.call "helper_split2" [trm {{ conj }}] G GL.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split2 : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split2.
all: elpi blind.
Qed.

(** -------------------- Arguments and Tactic Notation ------------------ *)

(**

  Elpi tactics can receive arguments

*)
Elpi Tactic print_args.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ Args) _ :- coq.say Args.
}}.
Elpi Typecheck.

Lemma test_print_args : True.
elpi print_args 1 x "a b" (1 = 0).
Abort.

(**
   The convention is that numbers like "1" are passed a "(int <arg>)",
   identifiers or strings are passed as "(str <arg>)" and terms
   have to be put between parentheses. This is what we get:

    [int 1, str x, str a b, 
    trm
      (app
      [global (indt «eq»), X0, 
        app [global (indc «S»), global (indc «O»)], global (indc «O»)])]

  remark that terms are received in raw format, eg before elaboration.
  Indeed the type argument to "eq" is a variable.
  One can use APIs like coq.elaborate-skeleton to infer holes like X0.

  See the "argument" data type in 
    https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi
  for a detailed decription of all the arguments a tactic can receive.
  
  Now let's write a tactic which behave pretty much like the "refine" one
  from Coq, but prints what it does.

*)

Elpi Tactic refine.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ [trm S] as G) GL :- !,
    coq.elaborate-skeleton S Ty T ok, % check S elaborates to T of type Ty (the goal)
    coq.say "Using" {coq.term->string T} "of type" {coq.term->string Ty},
    refine.no_check T G GL. % since T is already checked, we don't check it again
  solve _ _ :-
    coq.ltac.fail _ "does not fit".
}}.
Elpi Typecheck.

Lemma test_refine (P Q : Prop) (H : P -> Q) : Q.
Proof.
elpi refine (H _).
Abort.

(*
   It is customary to use the Tactic Notation command to attach to
   Elpi tactics a nicer syntax.
   
   In particular elpi tacname accepts as arguments the following bridges
   for Ltac

     - `ltac_string:(v)` (for `v` of type `string` or `ident`)
     - `ltac_int:(v)` (for `v` of type `int` or `integer`)
     - `ltac_term:(v)` (for `v` of type `constr` or `open_constr` or `uconstr` or `hyp`)
     - `ltac_(string|int|term)_list:(v)` (for `v` of type `list` of ...)

   Note that the Ltac type associates some semantics to the action of passing
   the arguments. For example "hyp" will accept an identifier only if it is
   an hypotheses of the context. While "uconstr" does not type check the term
   (it is typed anyway by the Elpi tactic).
*)

Tactic Notation "use" uconstr(t) :=
  elpi refine ltac_term:(t).

Tactic Notation "use" hyp(t) :=
  elpi refine ltac_term:(t).

Lemma test_use (P Q : Prop) (H : P -> Q) (p : P) : Q.
Proof.
use (H _).
Fail use q. (* no such hypothesis q *)
use p.
Qed.

Tactic Notation "print" uconstr_list_sep(l, ",") :=
  elpi print_args ltac_term_list:(l).

Lemma test_print (P Q : Prop) (H : P -> Q) (p : P) : Q.
print P, p, (H p).
Abort.

(** -------------- Examples: assumption and set ---------------- *)

Elpi Tactic assumption.
Elpi Accumulate lp:{{
  solve (goal Ctx _ Ty _ _ as G) GL :-
    std.mem Ctx (decl H _ Ty),
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof.
split.
elpi assumption.
Fail elpi assumption. (* Tactic failure: no such hypothesis. *)
Abort.

Elpi Tactic assumption2.
Elpi Accumulate lp:{{
  solve (goal Ctx _ Ty _ _ as G) GL :-
    std.mem Ctx (decl H _ Ty'), coq.unify-leq Ty' Ty ok,
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption2  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof.
split.
all: elpi assumption2.
Qed.

Elpi Tactic assumption3.
Elpi Accumulate lp:{{
  solve (goal Ctx _ _ _ _ as G) GL :-
    std.mem Ctx (decl H _ _),
    refine H G GL.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption3  (P Q : Prop) (p : P) (q : Q) : P /\ id Q.
Proof.
split.
all: elpi assumption3.
Qed.

Elpi Tactic find.
Elpi Accumulate lp:{{

solve (goal _ _ T _ [trm X]) _ :-
  pi x\
    copy X x => copy T (Tabs x),
    if (occurs x (Tabs x))
       (coq.say "found" {coq.term->string X})
       (coq.ltac.fail _ "not found").
}}.
Elpi Typecheck.

Lemma test_find (P Q : Prop) : P /\ P.
Proof.
elpi find (P).
Fail elpi find (Q).
elpi find (P /\ _).
Abort.

Elpi Tactic set.
Elpi Accumulate lp:{{

solve (goal _ _ T _ [str ID, trm X] as G) GL :-
  pi x\
    copy X x => copy T (Tabs x),
    if (occurs x (Tabs x))
       (coq.id->name ID Name,
        refine (let Name _ X x\ @cast _ (Tabs x)) G GL)
       (coq.ltac.fail _ "not found").

}}.
Elpi Typecheck.

Lemma test_set (P Q : Prop) : P /\ P.
Proof.
elpi set "x" (P).
unfold x.
Fail elpi set "y" (Q).
elpi set "y" (P /\ _).
Abort.

(**
   For more example of (basic) tactics written in Elpi see the eltac app:
     https://github.com/LPCIC/coq-elpi/tree/master/apps/eltac
*)

(** ------------------------ The proof state ----------------------------- *)

Elpi Tactic split.
Elpi Accumulate lp:{{
-  solve (goal _ RawProof {{ lp:A /\ lp:B }} Proof _) GL :- !,
-    RawProof = {{ conj _ _ }},                  % this triggers the elaboration
-    coq.ltac.collect-goals Proof GL _ShelvedGL, % Proof contains the elaborated
-    GL = [seal G1, seal G2],                    % we assert we have 2 subgoals
-    G1 = goal _ _ A _ _,                        % one for A
-    G2 = goal _ _ B _ _.                        % one for B in this order
+  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
+    refine {{ conj _ _ }} G GL.
  solve _ _ :-
    % This signals a failure in the Ltac model. A failure in Elpi, that
    % is no more cluases to try, is a fatal error that cannot be catch

   The last argument of "solve" is the list of subgoals, here we
   use the coq.ltac.collect-goals built-in to build it. The exact meaning of
   sealed-goal and the seal constructor is explained later on, in the section
   about tactic composition.

   This tactic was built, on purpose, using low level primitives.
   The orthodox way to build a tactic is to end it by calling refine
   or coq.ltac.call from
    https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi

   Lets rewrite split using refine
*)

Elpi Tactic split2.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    refine {{ conj _ _ }} G GL.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split2 : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split2.
all: elpi blind.
Show Proof.
Qed.

(*
    So refine, behind the scenes, assigns the trigger and collects the new
    goals. It comes in 3 variants, the regular one we just used, one in which
    the term is not elaborated but just typechecked and a last one
    where the term is not type checked at all (to be used with care, when
    performance is critical).

    coq.ltac.call lets one invoke ltac code, for example

*)


do split here assigning Proof and setting [] Gl, hint about type checking,
point fwd to proof state.

then talk about refine.

move this later

(*



  After that Elpi prints the proof state. The proof state is the collection of
  goals together with their types. In the side of Elpi this state is represented
  by constraints for the "evar" predicate.

   {c0 c1} :
   decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
   ?- evar (X0 c0 c1) 
       (app
         [global (indt «eq»), global (indt «nat»), 
          app [global (const «Nat.add»),
               c0, app [global (indc «S»), global (indc «O»)]],
          c1]) (X1 c0 c1)
      /* suspended on X0, X1 */

  One can recognize the set of bound variables "{c0 c1}", the hypothetical
  context of clauses about these variable (that also corresponds to the proof
  context), and finally the suspended goal "evar (X0 c0 c1) .. (X1 c0 c1)".

  The set of constraints on "evar" represents the Coq data structure called
  "sigma" (hence the name of the built-in to print it) that is used to
  represent the proof state in Coq. It is printed just afterwards:

   ...
   sigma =
    EVARS:
     ?X16==[x y |- x + 1 = y] (goal evar) {?Goal}
   ...
   Coq-Elpi mapping:
     ?X16 <-> X1

  The last part is a bijection between Coq's existential variables (AKA evars)
  and Elpi's unification variables. Coq uses the evar ?X16 in the example above
  to represent the (missing) proof of the goal. On the Elpi side X1 plays that
  role.

  One last thing to explain is why in Elpi the variable used to represent the
  goal is X0 while the one to represent the proof is X1. The meaning of the
  "evar" Elpi predicate linking the two is that the term assigned to the
  former has to be elaborated to the latter, that is the actual proof of the
  goal, when read back in Coq, should be a well typed term. This means that
  when an Elpi tactic  assigns a value to X0 some procedure to turn that
  value into X1 is triggered.
  That procedure is called elaboration and it is currently implemented by
  calling the coq.elaborate-skeleton built-in.

  Given this set up, it is impossible to use a term of the wrong type as a
  proof. Lets declare simle tactic that tries 0 and I as proof terms for a goal,
  without even looking at it.

*)



(** -------------------- msolve and tactic composition --------------------- *)

(*
   Since Coq 8.4 tactics can see more than one goal (multi-goal tactics).
   You can access this feature by using "all: tactic":
   - if the tactic is a regular one, it will be used on each goal independently
   - if the tactic is a multi-goal one, it will receive all goals

   In Elpi you can implement a multi-goal tactic by providing a clause for
   the "msolve" predicate. Since such tactic will need to manipulate multiple
   goals, potentially living in different proof context, it receives a list
   of sealed-goal, a data type which seals a goal and its proof context.

*)

Elpi Tactic ngoals.
Elpi Accumulate lp:{{

  msolve GL _ :-
    coq.say "#goals =" {std.length GL},
    coq.say GL.

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) : P /\ Q.
Proof.
split.
all: elpi ngoals.
Abort.

(*
   This simple tactic prints the number of goals it receives, as well as
   the list itself. We see something like

   #goals = 2
   [(nabla c0 \
      nabla c1 \
   	   seal
        (goal [decl c1 `Q` (sort prop), decl c0 `P` (sort prop)] (X0 c0 c1) c0 
          (X1 c0 c1) [])), 
    (nabla c0 \
      nabla c1 \
       seal
        (goal [decl c1 `Q` (sort prop), decl c0 `P` (sort prop)] (X2 c0 c1) c1 
          (X3 c0 c1) []))]
   
   nabla binds all proof variables, then seal holds a regular goal, which in
   turn carrier the context (the type of the proof variables).

   In order to operate inside a goal one can use uhe coq.ltac.open utility,
   which postulates all proof variables using pi and loads the goal context
   using =>.

   Operating on multiple goals is doable, but not easy. In particular the
   two proof context have to be related in some way. The following simple
   multi goal tactic shrinks the list of goals by removing duplicates.

*)

Elpi Tactic undup.
Elpi Accumulate lp:{{

  pred same-goal i:sealed-goal, i:sealed-goal.
  same-goal (nabla G1) (nabla G2) :- pi x\ same-goal (G1 x) (G2 x).
  same-goal (seal (goal Ctx1 _ Ty1 P1 _) as G1) (seal (goal Ctx2 _ Ty2 P2 _) as G2) :-
    same-ctx Ctx1 Ctx2,
    Ty1 == Ty2, % this is an elpi builtin, does not unify, just compare
    P1 = P2.

  pred same-ctx i:goal-ctx, i:goal-ctx.
  same-ctx [] [].
  same-ctx [decl V _ T1|C1] [decl V _ T2|C2] :- % we could compare up to permutation...
    T1 == T2,
    same-ctx C1 C2.

  pred undup i:sealed-goal, i:list sealed-goal, o:list sealed-goal.
  undup _ [] [].
  undup G [G1|GN] GN :- same-goal G G1.
  undup G [G1|GN] [G1|GL] :- undup G GN GL.

  msolve [G1|GS] [G1|GL] :-
    undup G1 GS GL. % we could find all duplicates, not just copies of the first one...

}}.
Elpi Typecheck.

Lemma test_undup (P Q : Prop) (p : P) (q : Q) : P /\ Q /\ P.
Proof.
repeat split.
Show Proof.
all: elpi undup.
Show Proof.
- apply p.
- apply q.
Qed.

(* 
   The two calls to show proof display, respectively:

    (fun (P Q : Prop) (p : P) (q : Q) => conj ?Goal (conj ?Goal0 ?Goal1))
    (fun (P Q : Prop) (p : P) (q : Q) => conj ?Goal0 (conj ?Goal ?Goal0))

  the proof term is the same but for the fact that after the tactic the first
  and last missing subterm (incomplete proof tree branch) are represented by
  the same hole. Indeed by solving one, we can also solve the other.

  On the notion of sealed-goal it is easy to define the usual LCF combinators,
  also known as Ltac tacticals. A few ones can be find in this file:
    https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi
  
  As we hinted before, tactic arguments are attached to the goal, since
  they can mention proof variables. So the Ltac code

    intro H; apply H.

  has to be seen as 3 steps, starting from a goal G:
  - introduction of H, obtaining G1
  - setting the argument H, obtaining G2
  - calling apply, obtaining G3

*)

Elpi Tactic argpass.
Elpi Accumulate lp:{{

 shorten coq.ltac.{ open, thenl, all }.

  type intro open-tactic. % goal -> list sealed-goal
  intro G GL :- refine {{ fun H => _ }} G GL.

  type set-arg-n-hyp int -> open-tactic.
  set-arg-n-hyp N (goal Ctx _ _ _ _ as G) [SG1] :-
    std.nth N Ctx (decl X _ _),
    coq.ltac.set-goal-arguments [trm X] G (seal G) SG1.

  type apply open-tactic.
  apply (goal _ _ _ _ [trm T] as G) GL :- refine T G GL.

  msolve SG GL :-
    all (thenl [ open intro, open (set-arg-n-hyp 0), open apply ]) SG GL.

}}.
Elpi Typecheck.

Lemma test_argpass (P : Prop) : P -> P.
Proof.
elpi argpass.
Qed.

(*
   Of course the tactic playing the role of "intro" could communicate back
   a datum to be passed to what follows

     thenl [ open (tac1 Datum), open (tac2 Datum) ]

   but the binder structure of sealed-goal would prevent Datum to mention
   proof variables, that would otherwise escape the sealing.

*)


(** -------------------- Tactic in terms --------------------- *)

(*
   Elpi tactics can be used inside terms via the usual ltac:(...)
   quotation, but can also be exported in the term grammar.

   Here we write a simple tactic for default values, which
   optionally takes a bound to the search depth.
*)

Elpi Tactic default.
Elpi Accumulate lp:{{

  pred default i:term, i:int, o:term.
  default _ 0 _ :- coq.error "max search depth reached".
  default {{nat}} _ {{46}}.
  default {{bool}} _ {{false}}.
  default {{list lp:A}} Max {{cons lp:D nil}} :-
    Max' is Max - 1, default A Max' D.

  solve (goal _ _ T _ [] as G) GL :-
    default T 9999 P,
    refine P G GL.

}}.
Elpi Typecheck.
Elpi Export default.

Definition foo : nat := default.
Definition bar : list bool := default.
Print foo.
Print bar.

(*
   The grammar entries for Elpi tactics in terms take an arbitrary
   number of arguments with the limitation that they are all terms:
   you can't pass a string or an integer as would normally do.

   Here we use Coq's primitive integers to pass the search depth
   (in a compact way).
*)

Elpi Accumulate default lp:{{
  solve (goal _ _ T _ [trm (primitive (uint63 Max))] as G) GL :-
    coq.uint63->int Max MaxI,    
    default T MaxI P,
    refine P G GL.
}}.
Elpi Typecheck.

From Coq Require Import  Int63.
Open Scope int63_scope.
Fail Definition baz : list nat := default 1. (* not enough*)
Definition baz : list nat := default 2.
Print baz.



