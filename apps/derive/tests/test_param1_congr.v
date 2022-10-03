From elpi.apps Require Import derive.param1_congr.

From elpi.apps Require Import test_derive_stdlib test_param1.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.


Module Coverage.

Elpi derive.param1.congr is_empty.
Elpi derive.param1.congr is_unit.
Elpi derive.param1.congr is_peano.
Elpi derive.param1.congr is_option.
Elpi derive.param1.congr is_pair.
Elpi derive.param1.congr is_seq.
Elpi derive.param1.congr is_box_peano.
Elpi derive.param1.congr is_nest.
Elpi derive.param1.congr is_rose.
Elpi derive.param1.congr is_rose_p.
Elpi derive.param1.congr is_rose_o.
Elpi derive.param1.congr is_w.
Elpi derive.param1.congr is_vect.
Elpi derive.param1.congr is_dyn.
Elpi derive.param1.congr is_zeta.
Elpi derive.param1.congr is_beta.
Elpi derive.param1.congr is_iota.
(*
Elpi derive.param1.congr is_large. (* slow *)
*)
Elpi derive.param1.congr is_prim_int.
Elpi derive.param1.congr is_prim_float.
Elpi derive.param1.congr is_fo_record.
Elpi derive.param1.congr is_pa_record.
Elpi derive.param1.congr is_pr_record.
Elpi derive.param1.congr is_dep_record.
Elpi derive.param1.congr is_enum.
Elpi derive.param1.congr is_bool.
Elpi derive.param1.congr is_eq.
Elpi derive.param1.congr is_sigma_bool.
Elpi derive.param1.congr is_ord.
Elpi derive.param1.congr is_val.
End Coverage.

Import Coverage.

Check congr_is_tt : is_tt = is_tt.

Check congr_is_Zero : is_Zero = is_Zero.
Check congr_is_Succ : forall x p1 p2, p1 = p2 -> is_Succ x p1 = is_Succ x p2.

Check congr_is_None : forall A PA, is_None A PA = is_None A PA.
Check congr_is_Some : forall A PA x p1 p2, p1 = p2 -> is_Some A PA x p1 = is_Some A PA x p2.

Check congr_is_Comma : forall A PA B PB x p1 p2, p1 = p2 -> forall y q1 q2, q1 = q2 -> is_Comma A PA B PB x p1 y q1 = is_Comma A PA B PB x p2 y q2.

Check congr_is_Nil : forall A PA, is_Nil A PA = is_Nil A PA.
Check congr_is_Cons : forall A PA x p1 p2, p1 = p2 -> forall y q1 q2, q1 = q2 -> is_Cons A PA x p1 y q1 = is_Cons A PA x p2 y q2.

Check congr_is_Leaf : forall A PA x p1 p2, p1 = p2 -> is_Leaf A PA x p1 = is_Leaf A PA x p2.
Check congr_is_Node : forall A PA x p1 p2, p1 = p2 -> is_Node A PA x p1 = is_Node A PA x p2.

Fail Check congr_is_NilN.
Fail Check congr_is_ConsN.

Check congr_is_via : forall A PA x p1 p2, p1 = p2 -> is_via A PA x p1 = is_via A PA x p2.

Check congr_is_VNil : forall A PA, is_VNil A PA = is_VNil A PA.
Fail Check congr_is_VCons.

Fail Check congr_is_box.

Check congr_is_Envelope : forall A PA x p1 p2, p1 = p2 -> forall y q1 q2, q1 = q2 -> is_Envelope A PA x p1 y q1 = is_Envelope A PA x p2 y q2. 

Check congr_is_Redex : forall A PA x p1 p2, p1 = p2 -> is_Redex A PA x p1 = is_Redex A PA x p2.

Fail Check congr_is_Why.

(* Check congr_is_K1 . *)

Check congr_is_PI.
Check congr_is_PF.

Check congr_is_Build_fo_record : forall n p1 p2, p1 = p2 -> forall b q1 q2, q1 = q2 -> is_Build_fo_record n p1 b q1= is_Build_fo_record n p2 b q2.
Check congr_is_Build_pa_record : forall A PA n p1 p2, p1 = p2 -> forall b q1 q2, q1 = q2 -> is_Build_pa_record A PA n p1 b q1= is_Build_pa_record A PA n p2 b q2.
Check congr_is_Build_pr_record : forall A pr n p1 p2, p1 = p2 -> forall b q1 q2, q1 = q2 -> is_Build_pr_record A pr n p1 b q1= is_Build_pr_record A pr n p2 b q2.
Check congr_is_E1 : is_E1 = is_E1.
