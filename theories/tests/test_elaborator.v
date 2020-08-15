From elpi Require Import elpi.

Elpi Command test.refiner.
Elpi Debug "OVERRIDE_COQ_ELABORATOR" "DBG:of".
Elpi Accumulate File "engine/elaborator.elpi".


Elpi Bound Steps 100000.
(* -------------------------------------------------------------*)
(* unit test *)
Elpi Query lp:{{
  pi a b c\ evar (X a b c) T (Y b). % to-restrict
}}.

(* -------------------------------------------------------------*)
(* tests on full terms *)

Elpi Query lp:{{
  {{plus}} = global (const GR), coq.env.const GR (some B) T,
  of B TY RB,
  coq.env.add-const "test_full_1" RB TY tt _
}}.

Elpi Query lp:{{
  {{plus_n_O}} = global (const GR), coq.env.const-body GR (some B),
  of B TY RB,
  coq.env.add-const "test_full_2" RB TY tt _
}}.

(* -------------------------------------------------------------*)
(* tests with implicit arguments *)

Elpi Query lp:{{
  of {{ fun x : lp:X => x }} TY RB,
  X = {{ nat }},
  coq.env.add-const "test_implicit_1" RB TY tt _
}}.

Elpi Query lp:{{
  of {{ fun x : _ => x + 0 }} TY RB,
  coq.env.add-const "test_implicit_2" RB TY tt _
}}.

(* -------------------------------------------------------------*)
(* test with universes *)

Elpi Query lp:{{
  of {{Type}} TY RB,
  coq.env.add-const "test_univ_1" RB TY tt _
}}.

Elpi Query lp:{{
   of {{Type}} S T, of {{Type}} T W,
   coq.env.add-const "test_univ_2" (@cast W T) T tt _
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
  fresh-ty X, fresh-ty Y, of X Y R,
  coq.env.add-const "test_univ_3" R Y tt _
}}.

(* -------------------------------------------------------------*)
(* tests with Coq coercions *)

Module Coercions.

Axiom T1 : Type.
Axiom T2 : nat -> Type.
Axiom T3 : bool -> Type.

Axiom f1 : T1 -> Type.
Axiom f3 : forall b, T3 b -> Type.

Axiom g1 : T1 -> nat -> nat.
Axiom g3 : forall b, T3 b -> nat -> nat.

Axiom h : forall n b, T2 n -> T3 b.

Coercion f1 : T1 >-> Sortclass.
Coercion f3 : T3 >-> Sortclass.
Coercion g1 : T1 >-> Funclass.
Coercion g3 : T3 >-> Funclass.
Coercion h : T2 >-> T3.

Elpi Query lp:{{
  get-option "of:coerce" tt =>
    of {{ fun (T : T1) (x : T) => x }} TY RB,
  coq.env.add-const "test_coercion_1" RB TY tt _.
}}.

Elpi Query lp:{{
  get-option "of:coerce" tt =>
    of {{ fun n (T : T3 n) (x : T) => x }} TY RB,
  coq.env.add-const "test_coercion_2" RB TY tt _.
}}.

Elpi Query lp:{{
  get-option "of:coerce" tt =>
    of {{ fun (T : T1) (x : nat) => T x }} TY RB,
  coq.env.add-const "test_coercion_3" RB TY tt _.
}}.

End Coercions.



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
(* tests with custom coercions *)

Elpi Query lp:{{ {{bool}} = global (indt GR), coq.env.indt GR A B C D E F }}.

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





