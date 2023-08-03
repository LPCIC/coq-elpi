From elpi.apps Require Import coercion.

Elpi Accumulate coercion.db lp:{{

coercion _ {{ true }} {{ bool }} {{ Prop }} {{ True }}.
coercion _ {{ false }} {{ bool }} {{ Prop }} {{ False }}.

}}.
Elpi Typecheck coercion.

Check true : Prop.
Check false : Prop.

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

(* To inspect already declared coercions, do *)
Elpi Print coercion "filename.html" "coercion".
(* then open filename.html with a browser and
   filter predicate "coercion" (using textbox on top left corner) *)

Elpi Disable Coercion.

Fail Check true : Prop.

Elpi Coercion coercion.

Check true : Prop.
