From elpi.apps Require Import coercion.

Elpi Accumulate coercion.db lp:{{

coercion _ {{ true }} {{ bool }} {{ Prop }} {{ True }}.
coercion _ {{ false }} {{ bool }} {{ Prop }} {{ False }}.

}}.
Elpi Typecheck coercion.

Check true : Prop.
Check false : Prop.

(* To inspect already declared coercions, do *)
Elpi Print coercion "filename.html" "coercion".
(* then open filename.html with a browser and
   filter predicate "coercion" (using textbox on top left corner) *)
