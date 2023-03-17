From elpi.tc.stdpp Require Import inj_hardcoded.
(* Elpi Bound Steps 1000. *)

Elpi Override TC HS_Inj.

Set Typeclasses Debug.

Check (_ : Inj eq1 eq3 (@compose nat nat nat g f)).
Check (_ : Inj _ _ (compose g g)).

Check (_ : Inj _ _ inr).
Check (_ : Inj eq eq (prod_map f f)).

Elpi Query lp:{{
  tc {{@Inj nat nat (@eq nat) (@eq nat) f}} Y.
}}.

Check (_ : Inj _ _ (prod_map g (compose f f))).

(* Definition inj_ex := Inj _ _ (prod_map (compose f g) (compose f f)). *)
(* Definition inj_ex := exists A B, Inj A B (prod_map (compose f g) (compose f f)). *)

Check (_ : Inj _ _ (prod_map (compose f g) (compose f f))).

Print HintDb typeclass_instances.
Goal Inj eq eq (prod_map (compose f g) (compose f f)).
Proof. typeclasses eauto. Qed.