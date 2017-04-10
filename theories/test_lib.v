From elpi Require Import elpi.

Elpi Init "./" "../elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "lp-lib.elpi".
Elpi Accumulate File "coq-lib.elpi".

(* lp *)

(* coq *)

Elpi Accumulate "
test-coq-env-typeof :-
  coq-locate ""nat"" (indt Nat),
  coq-locate ""O"" (indc Zero),
  coq-locate ""plus"" (const Plus),
  coq-env-typeof-gr Nat (sort _),
  coq-env-typeof-gr Zero (indt Nat),
  coq-env-typeof-gr Plus (prod _ (indt Nat) _\ prod _ (indt Nat) _\ (indt Nat)).
".
Elpi Run "test-coq-env-typeof".

Axiom empty : nat.

Elpi Accumulate "
test-coq-env-unfolds? :-
  coq-locate ""nat"" Nat,
  coq-locate ""empty"" Empty,
  coq-locate ""plus"" Plus,
  coq-env-unfolds? Plus,
  not (coq-env-unfolds? Nat),
  not (coq-env-unfolds? Empty).
".
Elpi Run "test-coq-env-unfolds?".

Elpi Run "
  subst-prod [foo,bar] (prod ""a"" t x\ prod ""b"" x y\ c x y) T1,
   T1 = (c foo bar),
  subst-lam [foo,bar] (lam ""a"" t x\ lam ""b"" x y\ c x y) T2,
   T2 = (c foo bar),
  prod-2-lam (prod ""a"" t x\ prod ""b"" x y\ c x y) T3,
   T3 = (lam ""a"" t x\ lam ""b"" x y\ c x y).
".

Elpi Run "
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO _,
  pp BO BO1.
".