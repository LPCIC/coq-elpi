From elpi.apps Require Import derive.eqb.

From elpi.apps.derive.tests Require Import test_derive_corelib test_eqType_ast test_tag test_fields.
Import test_derive_corelib.Coverage test_eqType_ast.Coverage test_tag.Coverage test_fields.Coverage.
    
Module Coverage.
Elpi derive.eqb empty.
Elpi derive.eqb unit.
Elpi derive.eqb peano.
Elpi derive.eqb option.
Elpi derive.eqb pair.
Elpi derive.eqb seq.
Elpi derive.eqb box_peano.
Elpi derive.eqb rose.
Elpi derive.eqb rose_p.
Elpi derive.eqb rose_o.
Fail Elpi derive.eqb nest.
Fail Elpi derive.eqb w.
Fail Elpi derive.eqb vect.
Fail Elpi derive.eqb dyn.
Fail Elpi derive.eqb zeta.
Elpi derive.eqb beta.
Fail Elpi derive.eqb iota.
(* slow
Elpi derive.eqb large.
*)
Elpi derive.eqb prim_int.
Fail Elpi derive.eqb prim_float.
Elpi derive.eqb prim_string.
Elpi derive.eqb fo_record.
Elpi derive.eqb pa_record.
Elpi derive.eqb pr_record.
Fail Elpi derive.eqb dep_record.
Elpi derive.eqb enum.
Fail Elpi derive.eqb eq.
Elpi derive.eqb bool.
Elpi derive.eqb sigma_bool.
Elpi derive.eqb sigma_bool2.
Elpi derive.eqb ord.
Elpi derive.eqb ord2.
Elpi derive.eqb val.
Elpi derive.eqb alias.
Elpi derive.eqb mempty.
Elpi derive.eqb munit.
Elpi derive.eqb mpeano.
Elpi derive.eqb moption.
Elpi derive.eqb mtree.


End Coverage.
Import Coverage.
From Corelib Require Import PosDef.

Notation eq_test T := (T -> T -> bool).
Notation eq_test2 T1 T2 := (T1 -> T2 -> bool).

Redirect "tmp" Check empty_eqb   : eq_test empty.
Redirect "tmp" Check unit_eqb    : eq_test unit.
Redirect "tmp" Check peano_eqb   : eq_test peano.
Redirect "tmp" Check option_eqb  : forall A, eq_test A -> eq_test (option A).
Redirect "tmp" Check pair_eqb    : forall A, eq_test A -> forall B, eq_test B -> eq_test (pair A B).
Redirect "tmp" Check seq_eqb     : forall A, eq_test A -> eq_test (seq A).
Redirect "tmp" Check rose_eqb    : forall A, eq_test A -> eq_test (rose A).
Fail Check nest_eqb.
(* Check w_eqb.   (* Do something but it is stupide*) *)
Fail Check vect_eqb    : forall A, eq_test A -> forall i, eq_test (vect A i).
Fail Check dyn_eqb.
Fail Check zeta_eqb : forall A, eq_test A -> eq_test (zeta A).
Redirect "tmp" Check beta_eqb : forall A, eq_test A -> eq_test (beta A).
Fail Check iota_eqb : eq_test iota.
(* Check large_eqb   : eq_test large. *)
(* FIXME : the definition of prim_int_eqb_fields*)
Redirect "tmp" Check prim_int_eqb    : eq_test prim_int.
Fail Check prim_float_eqb    : eq_test prim_float.
Redirect "tmp" Check fo_record_eqb : eq_test fo_record.

Redirect "tmp" Check pa_record_eqb : forall A, eq_test A -> eq_test (pa_record A).
Redirect "tmp" Check pr_record_eqb : forall A, eq_test A -> eq_test (pr_record A).
Redirect "tmp" Check enum_eqb : eq_test enum.
Redirect "tmp" Check sigma_bool_eqb : eq_test sigma_bool.
Redirect "tmp" Check ord_eqb : forall p1 p2, eq_test2 (ord p1) (ord p2).
Redirect "tmp" Check ord2_eqb : forall p1 p2, eq_test2 (ord2 p1) (ord2 p2).
Redirect "tmp" Check val_eqb : eq_test val.

Redirect "tmp" Check alias_eqb : eq_test alias.

Redirect "tmp" Check mempty_eqb : eq_test mempty.
Redirect "tmp" Check mempty'_eqb : eq_test mempty'.
Redirect "tmp" Check munit_eqb : eq_test munit.
Redirect "tmp" Check munit'_eqb : eq_test munit'.
Redirect "tmp" Check mpeano_eqb : eq_test mpeano.
Redirect "tmp" Check mpeano'_eqb : eq_test mpeano'.
Redirect "tmp" Check moption_eqb : forall A, eq_test A -> eq_test (moption A).
Redirect "tmp" Check moption'_eqb : forall A, eq_test A -> eq_test (moption' A).
Redirect "tmp" Check mtree_eqb : forall A, eq_test A -> eq_test (mtree A).
Redirect "tmp" Check mforest_eqb : forall A, eq_test A -> eq_test (mforest A).


Module EqbStandaloneFirst.

  Import test_derive_corelib.Mutual.Tree.

  Elpi derive.eqType.ast tree.
  Elpi derive.tag tree.
  Elpi derive.fields tree.
  Elpi derive.eqb tree.

  Redirect "tmp" Check tree_eqb : tree -> tree -> bool.
  Redirect "tmp" Check forest_eqb : forest -> forest -> bool.
  Redirect "tmp" Check tree_eqb_fields.
  Redirect "tmp" Check forest_eqb_fields.
  Redirect "tmp" Elpi Query derive.eqb lp:{{
    eqb-done {{:gref tree}},
    eqb-done {{:gref forest}}
  }}.
End EqbStandaloneFirst.

Module EqbStandaloneSecond.

  Import test_derive_corelib.Mutual.Tree.

  Elpi derive.eqType.ast tree.
  Elpi derive.tag tree.
  Elpi derive.fields tree.
  Elpi derive.eqb forest.

  Redirect "tmp" Check tree_eqb : tree -> tree -> bool.
  Redirect "tmp" Check forest_eqb : forest -> forest -> bool.
  Redirect "tmp" Check tree_eqb_fields.
  Redirect "tmp" Check forest_eqb_fields.
End EqbStandaloneSecond.

Module EqbComputation.

  Import test_derive_corelib.Mutual.Tree.

  Elpi derive.eqType.ast tree.
  Elpi derive.tag tree.
  Elpi derive.fields tree.
  Elpi derive.eqb tree.

  Example tree_eqb_refl_node : tree_eqb (node empty) (node empty) = true := eq_refl.
  Example forest_eqb_neq : forest_eqb empty (cons (node empty) empty) = false := eq_refl.
End EqbComputation.

Module EqbParametrized.

  Import test_derive_corelib.Mutual.ParametrizedTree.

  Elpi derive.eqType.ast ptree.
  Elpi derive.tag ptree.
  Elpi derive.fields ptree.
  Elpi derive.eqb ptree.

  Redirect "tmp" Check ptree_eqb : forall A, (A -> A -> bool) -> ptree A -> ptree A -> bool.
  Redirect "tmp" Check pforest_eqb : forall A, (A -> A -> bool) -> pforest A -> pforest A -> bool.
End EqbParametrized.

Module EqbUnsupportedValueParam.

  Inductive a (n : nat) : Type := ak (b0 : b n)
  with b (n : nat) : Type := bk (a0 : a n).

  Elpi derive.eqType.ast a.
  Elpi derive.tag a.
  Elpi derive.fields a.
  (* Value-parameterized mutual eqb is intentionally unsupported for now. *)
  Fail Elpi derive.eqb a.
End EqbUnsupportedValueParam.

Module EqbTripleFromBeta.

  Import test_derive_corelib.Mutual.CyclicTriple.

  Elpi derive.eqType.ast alpha.
  Elpi derive.tag alpha.
  Elpi derive.fields alpha.
  Elpi derive.eqb alpha.

  Redirect "tmp" Check alpha_eqb : alpha -> alpha -> bool.
  Redirect "tmp" Check beta_eqb : beta -> beta -> bool.
  Redirect "tmp" Check gamma_eqb : gamma -> gamma -> bool.
End EqbTripleFromBeta.

Module EqbTripleFromGamma.

  Import test_derive_corelib.Mutual.CyclicTriple.

  Elpi derive.eqType.ast gamma.
  Elpi derive.tag gamma.
  Elpi derive.fields gamma.
  Elpi derive.eqb gamma.

  Redirect "tmp" Check alpha_eqb : alpha -> alpha -> bool.
  Redirect "tmp" Check beta_eqb : beta -> beta -> bool.
  Redirect "tmp" Check gamma_eqb : gamma -> gamma -> bool.
End EqbTripleFromGamma.
