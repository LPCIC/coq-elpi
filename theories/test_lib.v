From elpi Require Import elpi.

Elpi Init "./" "../elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "lp-lib.elpi".
Elpi Accumulate File "coq-lib.elpi".

(* lp *)

(* coq *)

Elpi Accumulate "
test-coq-env-typeof :-
  coq-locate ""nat"" Nat,
  coq-locate ""O"" Zero,
  coq-locate ""plus"" Plus,
  coq-env-typeof Nat (sort _),
  coq-env-typeof Zero Nat,
  coq-env-typeof Plus (prod _ Nat _\ prod _ Nat _\ Nat).
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