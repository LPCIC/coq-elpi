From elpi.apps Require Import derive.param1 derive.param1_functor.

From elpi.apps.derive.tests Require Import test_derive_corelib test_param1.
Import test_derive_corelib.Coverage.
Import test_param1.Coverage.

Module Coverage.

Elpi derive.param1.functor is_empty.
Elpi derive.param1.functor is_unit.
Elpi derive.param1.functor is_peano.
Elpi derive.param1.functor is_option.
Elpi derive.param1.functor is_pair.
Elpi derive.param1.functor is_seq.
Elpi derive.param1.functor is_box_peano.
Elpi derive.param1.functor is_rose.
Elpi derive.param1.functor is_rose_p.
Elpi derive.param1.functor is_rose_o.
Elpi derive.param1.functor is_nest.
Fail Elpi derive.param1.functor is_w.
Elpi derive.param1.functor is_vect.
Elpi derive.param1.functor is_dyn.
Elpi derive.param1.functor is_zeta.
Elpi derive.param1.functor is_beta.
Elpi derive.param1.functor is_iota.
Elpi derive.param1.functor is_large.
Elpi derive.param1.functor is_prim_int.
Elpi derive.param1.functor is_prim_float.
Elpi derive.param1.functor is_fo_record.
Elpi derive.param1.functor is_pa_record.
Elpi derive.param1.functor is_pr_record.
Elpi derive.param1.functor is_dep_record.
Elpi derive.param1.functor is_enum.
Fail Elpi derive.param1.functor derive.param1.exports.is_eq.
Elpi derive.param1.functor derive.param1.exports.is_bool.
Elpi derive.param1.functor is_sigma_bool.
Elpi derive.param1.functor is_sigma_bool2.
Elpi derive.param1.functor is_ord.
Elpi derive.param1.functor is_ord2.
Elpi derive.param1.functor is_val.

End Coverage.

Local Notation func isT := (forall x, isT x -> isT x).
Local Notation func1 isT := (forall A P Q, (forall y : A, P y -> Q y) -> forall x, isT A P x -> isT A Q x).
Local Notation func2 isT := (forall A P Q, (forall y : A, P y -> Q y) -> forall A1 P1 Q1, (forall y : A1, P1 y -> Q1 y) -> forall x, isT A P A1 P1 x -> isT A Q A1 Q1 x).

Import Coverage.

Redirect "tmp" Check is_empty_functor : func is_empty.
Redirect "tmp" Check is_unit_functor : func is_unit.
Redirect "tmp" Check is_peano_functor : func is_peano.
Redirect "tmp" Check is_option_functor : func1 is_option.
Redirect "tmp" Check is_pair_functor : func2 is_pair.
Redirect "tmp" Check is_seq_functor : func1 is_seq.
Redirect "tmp" Check is_rose_functor : func1 is_rose.
Fail Check is_nest_functor : func1 is_nest.
Fail Check is_w_functor.

Redirect "tmp" Check is_vect_functor : forall A P Q, (forall y : A, P y -> Q y) -> forall i p (v : vect A i), is_vect A P i p v -> is_vect A Q i p v.
Redirect "tmp" Check is_dyn_functor : func is_dyn.
Redirect "tmp" Check is_zeta_functor : func1 is_zeta.
Redirect "tmp" Check is_beta_functor : func1 is_beta.
Redirect "tmp" Check is_iota_functor : func is_iota.
Redirect "tmp" Check is_large_functor : func is_large.
Redirect "tmp" Check is_prim_int_functor : func is_prim_int.
Redirect "tmp" Check is_prim_float_functor : func is_prim_float.

Redirect "tmp" Check is_fo_record_functor : func is_fo_record.
Redirect "tmp" Check is_pa_record_functor : func1 is_pa_record.
Redirect "tmp" Check is_pr_record_functor : func1 is_pr_record.
Redirect "tmp" Check is_enum_functor : func is_enum.
Redirect "tmp" Check is_ord_functor : forall n pn, func (is_ord n pn).
Redirect "tmp" Check is_ord2_functor : forall n pn, func (is_ord2 n pn).
Redirect "tmp" Check is_val_functor : func is_val.
