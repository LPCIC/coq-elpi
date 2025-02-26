From elpi.apps Require Import derive.param1 derive.eqOK.

From elpi.apps Require Import test_derive_corelib test_eqcorrect test_param1 test_param1_trivial.

Import test_derive_corelib.Coverage.
Import tests.test_eq.Coverage.
Import test_eqcorrect.Coverage.
Import test_param1.Coverage.
Import test_param1_trivial.Coverage.

Module Coverage.
Elpi derive.eqOK empty.
Elpi derive.eqOK unit.
Elpi derive.eqOK peano.
Elpi derive.eqOK option.
Elpi derive.eqOK pair.
Elpi derive.eqOK seq.
Elpi derive.eqOK box_peano.
Elpi derive.eqOK rose.
Elpi derive.eqOK rose_p.
Elpi derive.eqOK rose_o.
Fail Elpi derive.eqOK nest.
Fail Elpi derive.eqOK w.
Fail Elpi derive.eqOK vect.
Fail Elpi derive.eqOK dyn.
Elpi derive.eqOK zeta.
Elpi derive.eqOK beta.
Fail Elpi derive.eqOK iota.
(*
Elpi derive.eqOK large.
*)
Elpi derive.eqOK prim_int.
Fail Elpi derive.eqOK prim_float.
Elpi derive.eqOK prim_string.
Elpi derive.eqOK fo_record.
Elpi derive.eqOK pa_record.
Elpi derive.eqOK pr_record.
Fail Elpi derive.eqOK dep_record.
Elpi derive.eqOK enum.
Elpi derive.eqOK bool.
Fail Elpi derive.eqOK eq.
Fail Elpi derive.eqOK sigma_bool.
Fail Elpi derive.eqOK val.
Fail Elpi derive.eqOK ord.
End Coverage.

Import Coverage eqK.

Local Notation ok T F := (forall x, eq_axiom_at T F x).

Redirect "tmp" Check empty_eq_OK : ok empty empty_eq.
Redirect "tmp" Check unit_eq_OK : ok unit unit_eq.
Redirect "tmp" Check peano_eq_OK : ok peano peano_eq.
Redirect "tmp" Check option_eq_OK : forall A f, ok A f -> ok (option A) (option_eq A f).
Redirect "tmp" Check pair_eq_OK : forall A f, ok A f -> forall B g, ok B g -> ok (pair A B) (pair_eq A f B g).
Redirect "tmp" Check seq_eq_OK : forall A f, ok A f -> ok (seq A) (seq_eq A f).
Redirect "tmp" Check rose_eq_OK : forall A f, ok A f -> ok (rose A) (rose_eq A f).
Fail Check nest_eq_OK.
Fail Check w_eq_OK.
Fail Check vect_eq_OK.
Fail Check dyn_eq_OK.
Redirect "tmp" Check zeta_eq_OK : forall A f, ok A f -> ok (zeta A) (zeta_eq A f).
Redirect "tmp" Check beta_eq_OK : forall A f, ok A f -> ok (beta A) (beta_eq A f).
Fail Check iota_eq_OK.
(* Check large_eq_OK : ok large large_eq. *)
Redirect "tmp" Check prim_int_eq_OK.
Fail Check prim_float_eq_OK.

Redirect "tmp" Check fo_record_eq_OK : ok fo_record fo_record_eq.
Redirect "tmp" Check pa_record_eq_OK : forall A f, ok A f -> ok (pa_record A) (pa_record_eq A f).
Redirect "tmp" Check pr_record_eq_OK : forall A f, ok A f -> ok (pr_record A) (pr_record_eq A f).
Redirect "tmp" Check enum_eq_OK : ok enum enum_eq.

From elpi.apps Require Import test_param1_functor.
Import test_param1_functor.Coverage.

Set Uniform Inductive Parameters.

Module OtherTests.
Import test_param1_functor.Coverage.

Inductive dlist A := dnil | dcons (a : pair A peano) (l : dlist).

Elpi derive.param1 dlist.
Elpi derive.param1.congr is_dlist.
Elpi derive.param1.trivial is_dlist.
Elpi derive.induction dlist.
Elpi derive.projK dlist.
Elpi derive.bcongr dlist.
Elpi derive.isK dlist.
Elpi derive.param1.functor is_dlist.
Elpi derive.eq dlist.
Elpi derive.eqK dlist. 
Elpi derive.eqcorrect dlist.
Elpi derive.eqOK dlist dlist_eqOK.

Redirect "tmp" Check dlist_eqOK : 
  forall A f (h : forall l, eq_axiom_at A f l) l,
    eq_axiom_at (dlist A) (dlist_eq A f) l.

End OtherTests.
