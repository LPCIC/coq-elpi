From elpi Require Import derive.eqOK.

From elpi Require Import test_derive_stdlib test_eqcorrect test_param1 test_param1_inhab test_param1_trivial.

Import test_derive_stdlib.Coverage.
Import tests.test_eq.Coverage.
Import test_eqcorrect.Coverage.
Import test_param1.Coverage.
Import test_param1_inhab.Coverage.
Import test_param1_trivial.Coverage.

Module Coverage.
Elpi derive.eqOK empty.
Elpi derive.eqOK unit.
Elpi derive.eqOK peano.
Elpi derive.eqOK option.
Elpi derive.eqOK pair.
Elpi derive.eqOK seq.
Elpi derive.eqOK rose.
Fail Elpi derive.eqOK nest.
Fail Elpi derive.eqOK w.
Fail Elpi derive.eqOK vect.
Fail Elpi derive.eqOK dyn.
Elpi derive.eqOK zeta.
Elpi derive.eqOK beta.
Fail Elpi derive.eqOK iota.
Elpi derive.eqOK large.
End Coverage.

Import Coverage.

Local Notation ok T F := (forall x, eq_axiom T F x).

Check empty_eq_OK : ok empty empty_eq.
Check unit_eq_OK : ok unit unit_eq.
Check peano_eq_OK : ok peano peano_eq.
Check option_eq_OK : forall A f, ok A f -> ok (option A) (option_eq A f).
Check pair_eq_OK : forall A f, ok A f -> forall B g, ok B g -> ok (pair A B) (pair_eq A f B g).
Check seq_eq_OK : forall A f, ok A f -> ok (seq A) (seq_eq A f).
Check rose_eq_OK : forall A f, ok A f -> ok (rose A) (rose_eq A f).
Fail Check nest_eq_OK.
Fail Check w_eq_OK.
Fail Check vect_eq_OK.
Fail Check dyn_eq_OK.
Check zeta_eq_OK : forall A f, ok A f -> ok (zeta A) (zeta_eq A f).
Check beta_eq_OK : forall A f, ok A f -> ok (beta A) (beta_eq A f).
Fail Check iota_eq_OK.
Check large_eq_OK : ok large large_eq.

Module OtherTests.

From elpi Require Import test_param1_functor.
Import test_param1_functor.Coverage.

Inductive dlist A := dnil | dcons (a : pair A peano) (l : dlist A).

Elpi derive.param1 dlist.
Elpi derive.param1.inhab is_dlist.
Elpi derive.induction dlist.
Elpi derive.projK dlist.
Elpi derive.bcongr dlist.
Elpi derive.isK dlist.
Elpi derive.param1.functor is_dlist.
Elpi derive.eq dlist.
Elpi derive.eqK dlist. 
Elpi derive.eqcorrect dlist.
Elpi derive.eqOK dlist dlist_eqOK.

Check dlist_eqOK : 
  forall A f (h : forall l, eq_axiom A f l) l,
    eq_axiom (dlist A) (dlist_eq A f) l.

End OtherTests.