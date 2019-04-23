From elpi Require Import elpi.

Elpi Command test.refiner.

Elpi Accumulate File "engine/elaborator.elpi".

Elpi Bound Steps 10000.

(* -------------------------------------------------------------*)
(* tests on full terms (no pre-existing hole) *)

Elpi Query "
  {{plus}} = const GR, coq.env.const GR B T,
  of B TY RB.".

Elpi Query "
  {{plus_n_O}} = const GR, coq.env.const GR B T,
  of B TY RB".

(* -------------------------------------------------------------*)
(* tests with implicit arguments *)

Elpi Query "of {{fun x : _ => x}} T R".

Elpi Query "of {{fun x : _ => x + 0}} T R".

(* -------------------------------------------------------------*)
(* test with universes *)

Elpi Query "coq.say {{Type}}".

Elpi Query "of {{Type}} S T.".

Elpi Query "of {{Type}} S T, of {{Type}} T W,
            coq.typecheck (@cast W T) TW".

Elpi Query "X = {{Type}},
               std.assert! (not (of X X _)) ""Universe inconsistent""".

Elpi Accumulate "
  pred fresh-ty o:term.
  fresh-ty X :- X = {{Type}}.
".
Elpi Query "
  fresh-ty X, fresh-ty Y, of X Y _.
".

(* -------------------------------------------------------------*)
(* tests with HO unification *)

Axiom p : 0 = 0.

Elpi Query "
  of {{ @ex_intro _ _ _ p }} TY R,
  !, std.assert! (TY = 
    app [ {{ex}}, D, (lam _ D x0 \ {{@eq nat 0 0}})]) ""No skipping flex args"".
".

Elpi Query "
get-option ""unif:greedy"" tt => (
  of {{ @ex_intro _ _ 0 p }} TY R,
  !, std.assert! (TY = {{ @ex nat (fun n : nat => @eq nat n n) }}) ""Not greedy""
).
".


Elpi Query "
  of {{ exists n : nat, n = 0  }} _ TY,
  std.assert! (of {{ @ex_intro _ _ 0 p }} TY R) ""Not searching all solutions"".
".
 
Elpi Accumulate "
:before ""of:bidirectional-app"" % Like declaring an Arguments directive
bidir-app {{ex_intro}} Prod [_, _] Ty :-
  saturate-dummy Prod Ty1, unify-leq Ty1 Ty, !.
".

Elpi Query "
get-option ""unif:greedy"" tt => (
  of {{ exists n : nat, n = 0  }} _ TY,
  std.assert! (of {{ @ex_intro _ _ 0 p }} TY R) ""Not bidirectional""
).
".

(* -------------------------------------------------------------*)
(* tests with coercions *)

Elpi Query "{{bool}} = indt GR, coq.env.indt GR A B C D E F".

Axiom nat_of_bool : bool -> nat.

Elpi Accumulate "
  pred coercible o:term, o:term, o:term, o:term.
  coerce {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
  coerced {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
  coercible {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
".

Elpi Query "get-option ""of:coerce"" tt => (of {{true}} {{nat}} F).".

Axiom map : forall A B (F : A -> B), list A -> list B.
Open Scope list_scope.

Elpi Accumulate "
coerced {{list lp:X}} {{list lp:Y}} L R :-
  (pi x\ coerced X Y x (F x)),
  coq.say F,
  R = app[{{map}},X,Y,lam `x` X F,L].
".

Elpi Query "get-option ""of:coerce"" tt =>
  (of {{true :: nil}} {{list nat}} Res).
".

Axiom Z : Type.
Axiom Z_of_nat : nat -> Z.

Elpi Accumulate "
  coerce {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coerced {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coercible {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coerced X Y T F :- not(var X), not(var Y),
    coercible X Mid T FT, coerced Mid Y FT F.
".

Elpi Trace.
Elpi Query "get-option ""of:coerce"" tt => (of {{true}} {{Z}} Res). ".

Elpi Query "get-option ""of:coerce"" tt =>
  (of {{true :: nil}} {{list Z}} Res).
".

Axiom ring : Type.
Axiom carr : ring -> Type.

Elpi Accumulate "
  coerce {{ring}} (sort _) X {{carr lp:X}}.
  coerced {{ring}} (sort _) X {{carr lp:X}}.
  coercible {{ring}} (sort _) X {{carr lp:X}}.
".

Elpi Query "get-option ""of:coerce"" tt =>
  (of {{forall r : ring, forall x : r, x = x}} T R).
".





