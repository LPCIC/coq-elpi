From elpi.apps Require Import coercion.
#[warning="-deprecated-from-Coq"]
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
