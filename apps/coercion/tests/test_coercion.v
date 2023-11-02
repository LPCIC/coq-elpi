From elpi.apps Require Import coercion.
From Coq Require Import Bool.

Elpi Accumulate coercion.db lp:{{

coercion _ {{ True }} {{ Prop }} {{ bool }} {{ true }}.
coercion _ {{ False }} {{ Prop }} {{ bool }} {{ false }}.

}}.
Elpi Typecheck coercion.

Check True && False.

Parameter ringType : Type.
Parameter ringType_sort : ringType -> Type.
Parameter natmul : forall (R : ringType) (n : nat), (ringType_sort R).

Elpi Accumulate coercion.db lp:{{

coercion _ N {{ nat }} {{ ringType_sort lp:R }} {{ natmul lp:R lp:N }} :-
  coq.typecheck R {{ ringType }} ok.

}}.
Elpi Typecheck coercion.

Section TestNatMul.

Variable R : ringType.
Variable n : nat.

Check natmul R n : ringType_sort R.
Check n : ringType_sort R.

End TestNatMul.

Elpi Accumulate coercion.db lp:{{

coercion _ V T E {{ Nat.mul lp:V }} :-
  coq.unify-eq T {{ nat }} ok,
  coq.unify-eq E {{ nat -> nat }} ok.

coercion _ V T E {{ { m : nat | m < lp:V } }} :-
  coq.unify-eq T {{ nat }} ok,
  coq.unify-eq E {{ Type }} ok.

}}.
Elpi Typecheck coercion.

Check 3 2.
Check forall (x : 3), proj1_sig x < 3.

