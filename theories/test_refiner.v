From elpi Require Import elpi.


Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-refiner.elpi".

Elpi Bound Steps 10000.

(* -------------------------------------------------------------*)
(* tests on full terms (no pre-existing hole) *)

Elpi Run "
  {{plus}} = const GR, coq-env-const GR B T,
  of B TY RB.".

Elpi Run "
  {{plus_n_O}} = const GR, coq-env-const GR B T,
  of B TY RB".

(* -------------------------------------------------------------*)
(* tests with implicit arguments *)

Elpi Run "of {{fun x : _ => x}} T R".

Elpi Run "of {{fun x : _ => x + 0}} T R".

(* -------------------------------------------------------------*)
(* test with universes *)

Elpi Run "coq-say {{Type}}".

Elpi Run "of {{Type}} S T.".

Elpi Run "of {{Type}} S T, of {{Type}} T W,
            coq-typecheck (@cast W T) TW".

Elpi Run "X = {{Type}},
               assert (not (of X X _)) ""Universe inconsistent""".

Elpi Accumulate "
  fresh-ty X :- X = {{Type}}.
".
Elpi Run "
  fresh-ty X, fresh-ty Y, of X Y _.
".

(* -------------------------------------------------------------*)
(* tests with HO unification *)

Axiom p : 0 = 0.

Elpi Run "
  of {{ @ex_intro _ _ _ p }} TY R,
  !, assert (TY = 
    app [ {{ex}}, D, (lam _ D x0 \ {{@eq nat 0 0}})]) ""No skipping flex args"".
".

Elpi Run "
@with-option ""unif:greedy"" (
  of {{ @ex_intro _ _ 0 p }} TY R,
  !, assert (TY = {{ @ex nat (fun n : nat => @eq nat n n) }}) ""Not greedy""
).
".


Elpi Run "
  of {{ exists n : nat, n = 0  }} _ TY,
  assert (of {{ @ex_intro _ _ 0 p }} TY R) ""Not searching all solutions"".
".
 
Elpi Accumulate "
:before ""of:bidirectional-app"" % Like declaring an Arguments directive
bidir-app {{ex_intro}} Prod [_, _] Ty :-
  saturate-dummy Prod Ty1, unify-leq Ty1 Ty, !.
".

Elpi Run "
@with-option ""unif:greedy"" (
  of {{ exists n : nat, n = 0  }} _ TY,
  assert (of {{ @ex_intro _ _ 0 p }} TY R) ""Not bidirectional""
).
".

(* -------------------------------------------------------------*)
(* tests with coercions *)

Elpi Run "{{bool}} = indt GR, coq-env-indt GR A B C D E F".

Axiom nat_of_bool : bool -> nat.

Elpi Accumulate "
  coerce {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
".

Elpi Run "@with-option ""of:coerce"" (of {{true}} {{nat}} F).".

Axiom map : forall A B (F : A -> B), list A -> list B.
Open Scope list_scope.

Elpi Accumulate "
coerce {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
coerce {{list lp:X}} {{list lp:Y}} L R :-
  (pi x\ coerce X Y x (F x)),
  coq-say F,
  R = app[{{map}},X,Y,lam ""x"" X F,L].
".

Elpi Run "@with-option ""of:coerce""
  (of {{true :: nil}} {{list nat}} Res).
".

Axiom Z : Type.
Axiom Z_of_nat : nat -> Z.

Elpi Accumulate "
  coerce {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coerce X Y T F :- not($is_flex X), not($is_flex Y),
    coercible X Mid T FT, coerce Mid Y FT F.
".

Elpi Run "@with-option ""of:coerce"" 
  (of {{true}} {{Z}} Res).
".

Elpi Run "@with-option ""of:coerce""
  (of {{true :: nil}} {{list Z}} Res).
".

Axiom ring : Type.
Axiom carr : ring -> Type.

Elpi Accumulate "
  coerce {{ring}} (sort _) X {{carr lp:X}}.
".

Elpi Run "@with-option ""of:coerce""
  (of {{forall r : ring, forall x : r, x = x}} T R).
".





