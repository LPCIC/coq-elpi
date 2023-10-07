From elpi.apps Require Import tc.
From Coq Require Import Bool.

Elpi Accumulate typeclass.db lp:{{

typeclass _ {{ True }} {{ Prop }} {{ bool }} {{ true }}.
typeclass _ {{ False }} {{ Prop }} {{ bool }} {{ false }}.

}}.
Elpi Typecheck typeclass.

Check True && False.

Parameter ringType : Type.
Parameter ringType_sort : ringType -> Type.
Parameter natmul : forall (R : ringType) (n : nat), (ringType_sort R).

Elpi Accumulate typeclass.db lp:{{

typeclass _ N {{ nat }} {{ ringType_sort lp:R }} {{ natmul lp:R lp:N }} :-
  coq.typecheck R {{ ringType }} ok.

}}.
Elpi Typecheck typeclass.

Section TestNatMul.

Variable R : ringType.
Variable n : nat.

Check natmul R n : ringType_sort R.
Check n : ringType_sort R.

End TestNatMul.
