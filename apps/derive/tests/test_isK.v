From elpi.apps Require Import test_derive_corelib derive.isK.

Import test_derive_corelib.Coverage.

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
Elpi derive.isK prim_string.
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
Elpi derive.isK mempty.
Elpi derive.isK munit.
Elpi derive.isK mpeano.
Elpi derive.isK moption.
Elpi derive.isK mtree.
End Coverage.

Import Coverage.

Redirect "tmp" Check unit_is_tt : unit -> bool.

Redirect "tmp" Check peano_is_Zero : peano -> bool.
Redirect "tmp" Check peano_is_Succ : peano -> bool.

Redirect "tmp" Check option_is_None : forall A, option A -> bool.
Redirect "tmp" Check option_is_Some : forall A, option A -> bool.

Redirect "tmp" Check pair_is_Comma : forall A B, pair A B -> bool.

Redirect "tmp" Check seq_is_Nil : forall A, seq A -> bool.
Redirect "tmp" Check seq_is_Cons : forall A, seq A -> bool.

Redirect "tmp" Check rose_is_Leaf : forall A, rose A -> bool.
Redirect "tmp" Check rose_is_Node : forall A, rose A -> bool.

Redirect "tmp" Check nest_is_NilN : forall A, nest A -> bool.
Redirect "tmp" Check nest_is_ConsN : forall A, nest A -> bool.

Redirect "tmp" Check w_is_via : forall A, w A -> bool.

Redirect "tmp" Check vect_is_VNil : forall A i, vect A i -> bool.
Redirect "tmp" Check vect_is_VCons : forall A i, vect A i -> bool.

Redirect "tmp" Check dyn_is_box : dyn -> bool.

Redirect "tmp" Check zeta_is_Envelope : forall A, zeta A -> bool.

Redirect "tmp" Check beta_is_Redex : forall A, beta A -> bool.

Redirect "tmp" Check iota_is_Why : iota -> bool.

Redirect "tmp" Check large_is_K1.
Redirect "tmp" Check large_is_K2.

Redirect "tmp" Check prim_int_is_PI.
Redirect "tmp" Check prim_float_is_PF.

Redirect "tmp" Check fo_record_is_Build_fo_record : fo_record -> bool.
Redirect "tmp" Check pa_record_is_Build_pa_record : forall A, pa_record A -> bool.
Redirect "tmp" Check pr_record_is_Build_pr_record : forall A, pr_record A -> bool.
Redirect "tmp" Check enum_is_E1 : enum -> bool.

Set Universe Polymorphism.
Module UnivPoly.
Inductive I := TT.
Elpi derive.isK I.

Inductive Wrap := K : I -> Wrap.
Elpi derive.isK Wrap.

Inductive Prod (A B : Type) := PR : A -> B -> Prod A B.
Elpi derive.isK Prod.

Inductive Sum (A B : Type) := InL : A -> Sum A B | InR : B -> Sum A B.
Elpi derive.isK Sum.

Inductive List (A : Type) := Nil | Cons : A -> List A -> List A.
Elpi derive.isK List.
End UnivPoly.

Unset Universe Polymorphism.

From elpi.apps Require Import derive.

Module IsKStandaloneFirst.
  From elpi.apps Require Import derive.isK.

  Import test_derive_corelib.Mutual.NonRecursive.

  Elpi derive.isK color.

  Redirect "tmp" Check color_is_red : color -> bool.
  Redirect "tmp" Check color_is_blue : color -> bool.
  Redirect "tmp" Check shape_is_circle : shape -> bool.
  Redirect "tmp" Check shape_is_square : shape -> bool.
  Redirect "tmp" Elpi Query derive.isK lp:{{
    coq.locate "red" (indc R),
    coq.locate "circle" (indc C),
    isK-db R _,
    isK-db C _
  }}.
End IsKStandaloneFirst.

Module IsKStandaloneSecond.
  From elpi.apps Require Import derive.isK.

  Import test_derive_corelib.Mutual.NonRecursive.

  Elpi derive.isK shape.

  Redirect "tmp" Check color_is_red : color -> bool.
  Redirect "tmp" Check color_is_blue : color -> bool.
  Redirect "tmp" Check shape_is_circle : shape -> bool.
  Redirect "tmp" Check shape_is_square : shape -> bool.
End IsKStandaloneSecond.

Module IsKMetaFirst.
  From elpi.apps Require Import derive.isK.

  Import test_derive_corelib.Mutual.NonRecursive.

  #[only(isK)] derive color.

  Redirect "tmp" Check color_isk_red : color -> bool.
  Redirect "tmp" Check color_isk_blue : color -> bool.
  Redirect "tmp" Check shape_isk_circle : shape -> bool.
  Redirect "tmp" Check shape_isk_square : shape -> bool.
End IsKMetaFirst.

Module IsKMetaSecond.
  From elpi.apps Require Import derive.isK.

  Import test_derive_corelib.Mutual.NonRecursive.

  #[only(isK)] derive shape.

  Redirect "tmp" Check color_isk_red : color -> bool.
  Redirect "tmp" Check color_isk_blue : color -> bool.
  Redirect "tmp" Check shape_isk_circle : shape -> bool.
  Redirect "tmp" Check shape_isk_square : shape -> bool.
End IsKMetaSecond.

Module IsKPrefixSecond.
  From elpi.apps Require Import derive.isK.

  Import test_derive_corelib.Mutual.NonRecursive.

  #[only(isK), prefix="custom_"] derive shape.

  Redirect "tmp" Check color_isk_red : color -> bool.
  Redirect "tmp" Check color_isk_blue : color -> bool.
  Redirect "tmp" Check custom_isk_circle : shape -> bool.
  Redirect "tmp" Check custom_isk_square : shape -> bool.
End IsKPrefixSecond.

Module IsKPrefixCollision.
  From elpi.apps Require Import derive.isK.

  Inductive left : Type := same
  with right : Type := same_r.

  #[only(isK)] derive right.

  Redirect "tmp" Check left_isk_same : left -> bool.
  Redirect "tmp" Check right_isk_same_r : right -> bool.
End IsKPrefixCollision.
