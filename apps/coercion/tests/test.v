From elpi.apps Require Import coercion.
#[warning="-deprecated-from-Coq"]

Elpi Accumulate coercion.db lp:{{

coercion _ {{ True }} {{ Prop }} {{ bool }} {{ true }}.
coercion _ {{ False }} {{ Prop }} {{ bool }} {{ false }}.

}}.

Check andb True False.

Parameter ringType : Type.
Parameter ringType_sort : ringType -> Type.
Parameter natmul : forall (R : ringType) (n : nat), (ringType_sort R).

Elpi Accumulate coercion.db lp:{{

coercion _ N {{ nat }} {{ ringType_sort lp:R }} {{ natmul lp:R lp:N }} :-
  coq.typecheck R {{ ringType }} ok.

}}.

Section TestNatMul.

Variable R : ringType.
Variable n : nat.

Check natmul R n : ringType_sort R.
Check n : ringType_sort R.

End TestNatMul.


Axiom ord : nat -> Type.
Axiom bump : forall n, ord n -> ord (S n).

Elpi Accumulate coercion.db lp:{{

coercion _ X {{ ord lp:N }} {{ ord (S lp:N) }} {{ bump lp:N lp:X }}.

}}.



Check fun i : ord 1 => (i  : ord 2).
