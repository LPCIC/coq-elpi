From elpi Require Import elpi.

Elpi Command test.refiner.

Elpi Accumulate File "elpi/elpi-elaborator.elpi".


Elpi Bound Steps 10000.
(* -------------------------------------------------------------*)
(* tests on full terms *)

Elpi Query lp:{{
  {{plus}} = global (const GR) UI, coq.env.const GR UI (some B) T,
  of B TY RB.
}}.

Elpi Query lp:{{
  {{plus_n_O}} = global (const GR) UI, coq.env.const-body GR UI (some B),
  of B TY RB
}}.

(* -------------------------------------------------------------*)
(* tests with implicit arguments *)

Elpi Query lp:{{ of {{fun x : _ => x}} T R }}.

Elpi Query lp:{{ of {{fun x : _ => x + 0}} T R }}.

(* -------------------------------------------------------------*)
(* test with universes *)

Elpi Query lp:{{ coq.say {{Type}} }}.

Elpi Query lp:{{ of {{Type}} S T. }}.

Elpi Query lp:{{ 
   of {{Type}} S T, of {{Type}} T W,
   coq.typecheck (@cast W T) TW ok
}}.

Elpi Query lp:{{
  X = {{Type}},
  std.assert! (not (of X X _)) "Universe inconsistent"
}}.

Elpi Accumulate lp:{{
  pred fresh-ty o:term.
  fresh-ty X :- X = {{Type}}.
}}.
Elpi Query lp:{{
  fresh-ty X, fresh-ty Y, of X Y _.
}}.

(* -------------------------------------------------------------*)
(* tests with HO unification *)

Axiom p : 0 = 0.

Elpi Query lp:{{
  of {{ @ex_intro _ _ _ p }} TY R,
  !, std.assert! (TY = 
    app [ {{ex}}, D, (fun _ D x0 \ {{@eq nat 0 0}})]) "No skipping flex args".
}}.

Elpi Query lp:{{
get-option "unif:greedy" tt => (
  of {{ @ex_intro _ _ 0 p }} TY R,
  !, std.assert! (TY = {{ @ex nat (fun n : nat => @eq nat n n) }}) "Not greedy"
).
}}.

Elpi Query lp:{{
  of {{ exists n : nat, n = 0  }} _ TY,
  std.assert! (of {{ @ex_intro _ _ 0 p }} TY R) "Not searching all solutions".
}}.
 
Elpi Accumulate lp:{{
:before "of:bidirectional-app" % Like declaring an Arguments directive
bidir-app {{ex_intro}} Prod [_, _] Ty :-
  saturate-dummy Prod Ty1, unify-leq Ty1 Ty, !.
}}.

Elpi Query lp:{{
get-option "unif:greedy" tt => (
  of {{ exists n : nat, n = 0  }} _ TY,
  std.assert! (of {{ @ex_intro _ _ 0 p }} TY R) "Not bidirectional"
).
}}.

(* -------------------------------------------------------------*)
(* tests with coercions *)

Elpi Query lp:{{ {{bool}} = global (indt GR) UI, coq.env.indt GR UI A B C D E F }}.

Axiom nat_of_bool : bool -> nat.

Elpi Accumulate lp:{{
  pred coercible o:term, o:term, o:term, o:term.
  coerce {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
  coerced {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
  coercible {{bool}} {{nat}} X {{nat_of_bool lp:X}}.
}}.

Elpi Query lp:{{get-option "of:coerce" tt => (of {{true}} {{nat}} F).}}.

Axiom map : forall A B (F : A -> B), list A -> list B.
Open Scope list_scope.

Elpi Accumulate lp:{{
coerced {{list lp:X}} {{list lp:Y}} L R :-
  (pi x\ coerced X Y x (F x)),
  coq.say F,
  R = app[{{map}},X,Y,fun `x` X F,L].
}}.

Elpi Query lp:{{get-option "of:coerce" tt =>
  (of {{true :: nil}} {{list nat}} Res).
}}.

Axiom Z : Type.
Axiom Z_of_nat : nat -> Z.

Elpi Accumulate lp:{{
  coerce {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coerced {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coercible {{nat}} {{Z}} X {{Z_of_nat lp:X}}.
  coerced X Y T F :- not(var X), not(var Y),
    coercible X Mid T FT, coerced Mid Y FT F.
}}.

Elpi Query lp:{{get-option "of:coerce" tt => (of {{true}} {{Z}} Res). }}.

Elpi Query lp:{{get-option "of:coerce" tt =>
  (of {{true :: nil}} {{list Z}} Res).
}}.

Axiom ring : Type.
Axiom carr : ring -> Type.

Elpi Accumulate lp:{{
  coerce {{ring}} (sort _) X {{carr lp:X}}.
  coerced {{ring}} (sort _) X {{carr lp:X}}.
  coercible {{ring}} (sort _) X {{carr lp:X}}.
}}.

Elpi Query lp:{{get-option "of:coerce" tt =>
  (of {{forall r : ring, forall x : r, x = x}} T R).
}}.

(* primitive *)
From Coq Require Import Int63.
Elpi Query lp:{{ of {{ 99%int63 }} T X }}.
From Coq Require Import Floats.
Elpi Query lp:{{ of {{ 99.3e4%float }} T X }}.
Elpi Query lp:{{ whd1 {{ (99 + 1)%int63 }} {{ 100%int63 }} }}.
Elpi Query lp:{{ not(whd1 {{ (99 + _)%int63 }} _) }}.

