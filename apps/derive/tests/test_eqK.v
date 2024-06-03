From elpi Require Import elpi.
From elpi.apps Require Import derive.eqK.

From elpi.apps.derive.tests Require Import
  test_derive_stdlib
  test_isK
  test_projK
  test_bcongr
  test_eq.

Import test_derive_stdlib.Coverage.
Import test_isK.Coverage.
Import test_projK.Coverage.
Import test_bcongr.Coverage.
Import test_eq.Coverage.

Module Coverage.
Elpi derive.eqK empty.
Elpi derive.eqK unit.
Elpi derive.eqK peano.
Elpi derive.eqK option.
Elpi derive.eqK pair.
Elpi derive.eqK seq.
Elpi derive.eqK box_peano.
Elpi derive.eqK rose.
Elpi derive.eqK rose_p.
Elpi derive.eqK rose_o.
Fail Elpi derive.eqK nest.
Fail Elpi derive.eqK w.
Fail Elpi derive.eqK vect.
Fail Elpi derive.eqK dyn.
Elpi derive.eqK zeta.
Elpi derive.eqK beta.
Fail Elpi derive.eqK iota.
(*
Elpi derive.eqK large.
*)
Elpi derive.eqK prim_int.
Elpi derive.eqK prim_float.
Elpi derive.eqK fo_record.
Elpi derive.eqK pa_record.
Elpi derive.eqK pr_record.
Fail Elpi derive.eqK dep_record.
Elpi derive.eqK enum.
Fail Elpi derive.eqK sigma_bool.
Fail Elpi derive.eqK eq.
Elpi derive.eqK bool.
Fail Elpi derive.eqK val.
Fail Elpi derive.eqK ord.
End Coverage.

Import Coverage.
Import test_eq.Coverage.

Redirect "tmp" Check eq_axiom_tt : eq_axiom_at unit unit_eq tt.

Redirect "tmp" Check eq_axiom_Zero : eq_axiom_at peano peano_eq Zero.
Redirect "tmp" Check eq_axiom_Succ : forall y, eq_axiom_at peano peano_eq y -> eq_axiom_at peano peano_eq (Succ y).

Redirect "tmp" Check eq_axiom_None : forall A f, eq_axiom_at (option A) (option_eq A f) (None A).
Redirect "tmp" Check eq_axiom_Some : forall A f x, eq_axiom_at A f x -> eq_axiom_at (option A) (option_eq A f) (Some A x).

Redirect "tmp" Check eq_axiom_Comma: forall A f B g, forall x, eq_axiom_at A f x -> forall y, eq_axiom_at B g y -> eq_axiom_at (pair A B) (pair_eq A f B g) (Comma A B x y).

Redirect "tmp" Check eq_axiom_Nil: forall A f, eq_axiom_at (seq A) (seq_eq A f) (Nil A).
Redirect "tmp" Check eq_axiom_Cons : forall A f x, eq_axiom_at A f x -> forall xs, eq_axiom_at (seq A) (seq_eq A f) xs -> eq_axiom_at (seq A) (seq_eq A f) (Cons A x xs).

Redirect "tmp" Check eq_axiom_Leaf: forall A f a, eq_axiom_at A f a -> eq_axiom_at (rose A) (rose_eq A f) (Leaf A a).
Redirect "tmp" Check eq_axiom_Node: forall A f l, eq_axiom_at (seq (rose A)) (seq_eq (rose A) (rose_eq A f)) l -> eq_axiom_at (rose A) (rose_eq A f) (Node A l).

Redirect "tmp" Check eq_axiom_Envelope.

Redirect "tmp" Check eq_axiom_Redex.

(*Check eq_axiom_K1.*)

Redirect "tmp" Check eq_axiom_PI.
Redirect "tmp" Check eq_axiom_PF.

Redirect "tmp" Check eq_axiom_Build_fo_record : forall x, eq_axiom_at peano peano_eq x -> forall y, eq_axiom_at unit unit_eq y ->  eq_axiom_at fo_record fo_record_eq (Build_fo_record x y).
Redirect "tmp" Check eq_axiom_Build_pa_record : forall A f, forall x, eq_axiom_at peano peano_eq x -> forall y, eq_axiom_at A f y -> eq_axiom_at (pa_record A) (pa_record_eq A f) (Build_pa_record A x y).
Redirect "tmp" Check eq_axiom_Build_pr_record : forall A f, forall x, eq_axiom_at peano peano_eq x -> forall y, eq_axiom_at A f y -> eq_axiom_at (pr_record A) (pr_record_eq A f) (Build_pr_record A x y).

Redirect "tmp" Check eq_axiom_E1 : eq_axiom_at enum enum_eq E1.
Redirect "tmp" Check eq_axiom_E2 : eq_axiom_at enum enum_eq E2.
Redirect "tmp" Check eq_axiom_E3 : eq_axiom_at enum enum_eq E3.
