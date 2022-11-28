From elpi.apps Require Import test_derive_stdlib derive.isK.

Import test_derive_stdlib.Coverage.

(* coverage *)
Module Coverage.
Elpi derive.isK empty.
Elpi derive.isK unit.
Elpi derive.isK peano.
Elpi derive.isK option.
Elpi derive.isK pair.
Elpi derive.isK seq.
Elpi derive.isK box_peano.
Elpi derive.isK rose.
Elpi derive.isK rose_p.
Elpi derive.isK rose_o.
Elpi derive.isK nest.
Elpi derive.isK w.
Elpi derive.isK vect.
Elpi derive.isK dyn.
Elpi derive.isK zeta.
Elpi derive.isK beta.
Elpi derive.isK iota.
Elpi derive.isK large.
Elpi derive.isK prim_int.
Elpi derive.isK prim_float.
Elpi derive.isK fo_record.
Elpi derive.isK pa_record.
Elpi derive.isK pr_record.
Elpi derive.isK dep_record.
Elpi derive.isK enum.
Elpi derive.isK bool.
Elpi derive.isK eq.
Elpi derive.isK sigma_bool.
Elpi derive.isK ord.
Elpi derive.isK val.
End Coverage.

Import Coverage.

Check unit_is_tt : unit -> bool.

Check peano_is_Zero : peano -> bool.
Check peano_is_Succ : peano -> bool.

Check option_is_None : forall A, option A -> bool.
Check option_is_Some : forall A, option A -> bool.

Check pair_is_Comma : forall A B, pair A B -> bool.

Check seq_is_Nil : forall A, seq A -> bool.
Check seq_is_Cons : forall A, seq A -> bool.

Check rose_is_Leaf : forall A, rose A -> bool.
Check rose_is_Node : forall A, rose A -> bool.

Check nest_is_NilN : forall A, nest A -> bool.
Check nest_is_ConsN : forall A, nest A -> bool.

Check w_is_via : forall A, w A -> bool.

Check vect_is_VNil : forall A i, vect A i -> bool.
Check vect_is_VCons : forall A i, vect A i -> bool.

Check dyn_is_box : dyn -> bool.

Check zeta_is_Envelope : forall A, zeta A -> bool.

Check beta_is_Redex : forall A, beta A -> bool.

Check iota_is_Why : iota -> bool.

Check large_is_K1.
Check large_is_K2.

Check prim_int_is_PI.
Check prim_float_is_PF.

Check fo_record_is_Build_fo_record : fo_record -> bool.
Check pa_record_is_Build_pa_record : forall A, pa_record A -> bool.
Check pr_record_is_Build_pr_record : forall A, pr_record A -> bool.
Check enum_is_E1 : enum -> bool.


