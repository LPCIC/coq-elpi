From Corelib Require Import Nat BinNums.
Definition bool_is_true := is_true.
From elpi.apps.derive.tests Require Import test_derive_corelib.
From elpi.apps Require Import
  derive
  derive.tag
  derive.isK
  derive.projK
  derive.map
  derive.param1
  derive.param1_congr
  derive.param1_functor
  derive.param2
  derive.induction.

Module StandaloneTagIsKProjK.
  Import test_derive_corelib.Mutual.Indexed.

  Elpi derive.tag itree.
  Redirect "tmp" Check itree_tag : forall A n, itree A n -> positive.
  Redirect "tmp" Check iforest_tag : forall A n, iforest A n -> positive.

  Elpi derive.isK itree.
  Redirect "tmp" Check itree_is_ileaf : forall A n, itree A n -> bool.
  Redirect "tmp" Check itree_is_inode : forall A n, itree A n -> bool.
  Redirect "tmp" Check iforest_is_inil : forall A n, iforest A n -> bool.
  Redirect "tmp" Check iforest_is_icons : forall A n, iforest A n -> bool.

  Elpi derive.projK itree.
  Redirect "tmp" Check projileaf1.
  Redirect "tmp" Check projinode1.
  Redirect "tmp" Check projinode2.
  Redirect "tmp" Check iforest_getk_icons1.
  Redirect "tmp" Check iforest_getk_icons2.
End StandaloneTagIsKProjK.

Module StandaloneMap.
  Import test_derive_corelib.Mutual.Indexed.

  Elpi derive.map itree.
  Redirect "tmp" Check itree_map : forall A B, (A -> B) -> forall n, itree A n -> itree B n.
  Redirect "tmp" Check iforest_map : forall A B, (A -> B) -> forall n, iforest A n -> iforest B n.

  Example itree_map_computes :
    itree_map nat bool Nat.even 0 (ileaf nat 2) = ileaf bool true.
  Proof. vm_compute. reflexivity. Qed.
End StandaloneMap.

Module StandaloneParam1Param2.
  Import test_derive_corelib.Mutual.Indexed.

  Elpi derive.param1 nat.
  Elpi derive.param1 itree.
  Redirect "tmp" Check is_itree : forall A, (A -> Type) -> forall n, is_nat n -> itree A n -> Type.
  Redirect "tmp" Check is_iforest : forall A, (A -> Type) -> forall n, is_nat n -> iforest A n -> Type.

  Elpi derive.param2 nat.
  Elpi derive.param2 itree.
  Redirect "tmp" Check itree_R :
    forall A1 A2, (A1 -> A2 -> Type) ->
    forall n1 n2, nat_R n1 n2 -> itree A1 n1 -> itree A2 n2 -> Type.
  Redirect "tmp" Check iforest_R :
    forall A1 A2, (A1 -> A2 -> Type) ->
    forall n1 n2, nat_R n1 n2 -> iforest A1 n1 -> iforest A2 n2 -> Type.
End StandaloneParam1Param2.

Module StandaloneParam1CongrFunctorInduction.
  Import test_derive_corelib.Mutual.Indexed.

  Elpi derive.param1 nat.
  Elpi derive.param1 itree.
  Elpi derive.param1.congr is_itree.
  Redirect "tmp" Check congr_is_ileaf.
  Redirect "tmp" Check congr_is_inil.

  Elpi derive.param1.functor is_itree.
  Redirect "tmp" Check is_itree_functor : forall A (PA PB : A -> Type),
    (forall x, PA x -> PB x) -> forall n pn x, is_itree A PA n pn x -> is_itree A PB n pn x.
  Redirect "tmp" Check is_iforest_functor : forall A (PA PB : A -> Type),
    (forall x, PA x -> PB x) -> forall n pn x, is_iforest A PA n pn x -> is_iforest A PB n pn x.

  Elpi derive.induction itree.
  Redirect "tmp" Check itree_induction.
  Redirect "tmp" Check iforest_induction.
End StandaloneParam1CongrFunctorInduction.

Module HookMap.
  Import test_derive_corelib.Mutual.Indexed.

  #[only(map)] derive itree.
  Redirect "tmp" Check itree_map : forall A B, (A -> B) -> forall n, itree A n -> itree B n.
  Redirect "tmp" Check iforest_map : forall A B, (A -> B) -> forall n, iforest A n -> iforest B n.
End HookMap.

Module HookInduction.
  Import test_derive_corelib.Mutual.Indexed.

  Elpi derive.param1 nat.
  #[only(induction)] derive itree.
  Redirect "tmp" Check is_itree_functor : forall A (PA PB : A -> Type),
    (forall x, PA x -> PB x) -> forall n pn x, is_itree A PA n pn x -> is_itree A PB n pn x.
  Redirect "tmp" Check itree_induction.
  Redirect "tmp" Check iforest_induction.
End HookInduction.
