From elpi Require Import test_derive_stdlib derive.isK.

Import test_derive_stdlib.Coverage.

(* coverage *)
Module Coverage.
Elpi derive.isK empty.
Elpi derive.isK unit.
Elpi derive.isK peano.
Elpi derive.isK option.
Elpi derive.isK pair.
Elpi derive.isK seq.
Elpi derive.isK rose.
Elpi derive.isK nest.
Elpi derive.isK w.
Elpi derive.isK vect.
Elpi derive.isK dyn.
Fail Elpi derive.isK zeta.
Elpi derive.isK beta.
Elpi derive.isK iota.
Elpi derive.isK large.
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

Fail Check zeta_is_Envelope.

Check beta_is_Redex : forall A, beta A -> bool.

Check iota_is_Why : iota -> bool.

Check large_is_K1.
Check large_is_K2.



