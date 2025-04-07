From elpi Require Export elpi.
From elpi.core Require Import ssreflect ssrfun ssrbool.

Ltac ltac_foo := cut True; [ idtac | abstract (exact I) ].

Record fooType := Foo { sort :> Type; }.
Canonical unit_fooType := Foo unit.

Elpi Tactic fail_foo.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [_] as G) GS :-
  coq.ltac.call "ltac_foo" [] G GS.

}}.


Goal nat.
Proof.
elpi fail_foo ([the fooType of unit : Type]).
exact (fun _ => 0).
Qed.
