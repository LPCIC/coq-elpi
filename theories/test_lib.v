From elpi Require Import elpi.


Elpi Accumulate File "coq-lib.elpi".

(* lp *)

Fail Elpi Run "nth 3 [a,b] X".
Elpi Run "nth 1 [a,b] b".
Elpi Run "ignore-failure fail".
Elpi Run "map2 [1,2,3] [a,b,c] (x\y\res\ res = [x,y]) [[1,a],[2,b],[3,c]]".
Elpi Run "fold [1,2,3] 0 (i\acc\res\res is i + acc) 6".
Elpi Run "fold2 [1,2] [3,4] 0 (i\j\acc\res\res is i + j + acc) 10".
Elpi Run "split-at 2 [a,b,c,d,e] [a,b] [c,d,e]".
Elpi Run "
  L = [a,b,c,d,e],
  N = 2,
  split-at N L {take N L} {drop N L}
".
Elpi Run "append [a,b] [c,d] [a,b,c,d]".
Elpi Run "rev [a,b,c] [c,b,a]".
Elpi Run "if (a = b) fail true".
Fail Elpi Run "if (a = a) fail true".
Elpi Run "map-i [a,b] (n\_\x\x = n) [0,1]".

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
  prod->lam (prod ""a"" t x\ prod ""b"" x y\ c x y) T3,
   T3 = (lam ""a"" t x\ lam ""b"" x y\ c x y).
".

Elpi Run "
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO _,
  pp BO BO1.
".

Elpi Run "mk-app (app [f,x]) [y,z] (app[f,x,y,z])".
Elpi Run "mk-app X [a,b] F, not (F = app L)".

Elpi Run "safe-dest-app x x []".
Elpi Run "safe-dest-app (app [x,y]) x [y]".

