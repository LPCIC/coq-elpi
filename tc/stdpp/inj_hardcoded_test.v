From elpi.tc.stdpp Require Import inj_hardcoded.
From elpi Require Import elpi.
(* Elpi Bound Steps 1000. *)

Elpi Debug "debug".

Set Printing All.
Check (_ : Inj _ _ g).
Check (_ : Inj _ _ inr). 

Check (_ : Inj _ _ (@compose nat nat nat g f)).
Check (_ : Inj _ _ (compose g f)).
Check (_ : Inj _ _ (prod_map (compose f g) (compose f f))).
(* Check (_ : Inj _ _ _). *)

Check (_ : Inj eq eq (prod_map f f)).

Check (_ : Inj _ _ (prod_map g (compose f f))).

(* Definition inj_ex := Inj _ _ (prod_map (compose f g) (compose f f)). *)
(* Definition inj_ex := exists A B, Inj A B (prod_map (compose f g) (compose f f)).

Check (_ : Inj _ _ (prod_map (compose f g) (compose f f))).

Goal Inj eq eq (prod_map (compose f g) (compose f f)).
Proof. typeclasses eauto. Qed. *)