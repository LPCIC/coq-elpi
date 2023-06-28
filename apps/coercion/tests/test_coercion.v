From elpi.apps Require Import coercion.

Elpi Accumulate Coercion lp:{{

coercion _ {{ true }} {{ bool }} {{ Prop }} {{ True }}.
coercion _ {{ false }} {{ bool }} {{ Prop }} {{ False }}.

}}.
Elpi Typecheck Coercion.

Check true : Prop.
Check false : Prop.

Parameter ringType : Type.
Parameter ringType_sort : ringType -> Type.
Parameter natmul : forall (R : ringType) (n : nat), (ringType_sort R).

Elpi Accumulate Coercion lp:{{

coercion _ N {{ nat }} {{ ringType_sort lp:R }} {{ natmul lp:R lp:N }} :-
  coq.typecheck R {{ ringType }} ok.

}}.
Elpi Typecheck Coercion.

Section TestNatMul.

Variable R : ringType.
Variable n : nat.

Check natmul R n : ringType_sort R.
Check n : ringType_sort R.

End TestNatMul.
