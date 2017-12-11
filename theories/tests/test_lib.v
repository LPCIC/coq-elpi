From elpi Require Import elpi.

Elpi Command test.lib.

Elpi Accumulate "
kind term type.
type a,b,c,d,e,foo,bar,t,x,y,z term.
type f term -> term -> term.
".
(* lp *)

Fail Elpi Query "nth 3 [a,b] X".
Elpi Query "nth 1 [a,b] b".
Elpi Query "ignore-failure fail".
Elpi Query "map2 [1,2,3] [a,b,c] (x\y\res\ res = pr x y) [pr 1 a,pr 2 b, pr 3 c]]".
Elpi Query "fold [1,2,3] 0 (i\acc\res\res is i + acc) 6".
Elpi Query "fold2 [1,2] [3,4] 0 (i\j\acc\res\res is i + j + acc) 10".
Elpi Query "split-at 2 [a,b,c,d,e] [a,b] [c,d,e]".
Elpi Query "
  L = [a,b,c,d,e],
  N = 2,
  split-at N L {take N L} {drop N L}
".
Elpi Query "append [a,b] [c,d] [a,b,c,d]".
Elpi Query "rev [a,b,c] [c,b,a]".
Elpi Query "if (a = b) fail true".
Fail Elpi Query "if (a = a) fail true".
Elpi Query "map-i [a,b] (n\_\x\x = n) [0,1]".

Elpi Query "not(do! [(X = 1; X = 2), X = 2])".
Elpi Query "not(spy-do! [(X = 1; X = 2), X = 2])".

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
Elpi Query "test-coq-env-typeof".

Elpi Query "
  coq-string->name ""a"" A,
  coq-string->name ""b"" B,
  subst-prod [foo,bar] (prod A t x\ prod B x y\ f x y) T1,
   T1 = (f foo bar),
  subst-lam [foo,bar] (lam A t x\ lam B x y\ f x y) T2,
   T2 = (f foo bar),
  prod->lam (prod A t x\ prod B x y\ f x y) T3,
   T3 = (lam A t x\ lam B x y\ f x y).
".

Elpi Query "
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO _,
  pp BO BO1.
".

Elpi Query "mk-app (app [a,x]) [y,z] (app[a,x,y,z])".
Elpi Query "mk-app X [a,b] F, not (F = app L)".

Elpi Query "safe-dest-app x x []".
Elpi Query "safe-dest-app (app [x,y]) x [y]".

Elpi Query "prod->lam (prod X T F) L, L = lam _ _ _".

Require Vector.

Elpi Accumulate "
test-env-indt :-
  coq-locate ""Vector.t"" Vect, Vect = indt GR,
  coq-locate ""Vector.nil"" Vnil,
  coq-locate ""Vector.cons"" Vcons,
  coq-locate ""nat"" Nat,
  coq-locate ""O"" Zero,
  coq-locate ""S"" Succ,
  coq-env-indt GR tt 1 1 TY [Vnil,Vcons] [Tnil,Tcons],
  TY = (prod _ (sort _) _\ prod _ Nat _\ (sort _)),
  Tnil = (prod _ (sort _) a\ app [Vect,a,Zero]),
  Tcons = (prod _ (sort _) a\
           prod _ a v\
           prod _ Nat n\
           prod _ (app[Vect,a,n]) v\
            app[Vect,a,app[Succ,n]]).
".
Elpi Query "test-env-indt".


Elpi Accumulate "
test-env-indc :-
  coq-locate ""nat"" Nat,
  coq-locate ""S"" Succ,
  coq-locate ""Vector.t"" Vect,
  coq-locate ""Vector.cons"" (indc GR),
  coq-env-indc GR 1 1 1
          (prod _ (sort _) a\
           prod _ a v\
           prod _ Nat n\
           prod _ (app[Vect,a,n]) v\
            app[Vect,a,app[Succ,n]]).
".
Elpi Query "test-env-indc".

Elpi Accumulate "
test-env-indc1 :-
  coq-locate ""Vector.nil"" (indc GR),
  coq-env-indc GR 1 1 0 _.
".
Elpi Query "test-env-indc1".


Elpi Command mk_identity_match "

main [str A] :-
  coq-locate ""Vector.t"" (indt GR),
  T = (lam `T` {{Type}} t\
       lam `n` {{nat}} n\
       lam `v` (app[indt GR,t,n]) v\
        {build-match-skeleton v GR [t,n]
             (_\ _\ ty\ r\ rev ty [r|_])    % the same type of the matched term
          (k\ _\ v\ _ \ r\ mk-app k v r)}), % the constructor applied to the vars
  coq-elaborate T T1 _,
  coq-env-add-const A T1 _ _ _.

".

Elpi mk_identity_match foo.

Lemma test_foo (v := Vector.cons nat 3 0 (Vector.nil nat)) : foo _ _ v = v.
Proof.
reflexivity.
Qed.

