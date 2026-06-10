(* This is the same derivation set exported by derive.std, kept explicit so
   each standard derivation is tested independently.  Each derive call below
   lives in its own module and is checked against a signature documenting the
   Coq definitions that derivation is expected to add. *)
From Corelib Require Import BinNums Nat ssrbool.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook_for_mutual_wrapper_test.
From elpi.apps.derive.elpi Extra Dependency "derive.elpi" as derive_core_for_mutual_wrapper_test.
From elpi.apps Require Import
  derive
  derive.map
  derive.lens
  derive.lens_laws
  derive.param1
  derive.param1_congr
  derive.param1_trivial
  derive.param1_functor
  derive.param2
  derive.induction
  derive.tag
  derive.fields
  derive.eqb
  derive.eqbcorrect
  derive.eqbOK
  derive.isK
  derive.projK
  derive.bcongr.

Elpi Command derive_mutual_wrapper_test.
#[synterp] Elpi Accumulate lp:{{
  main _ :- coq.env.begin-module "wleft" none, coq.env.end-module _.
}}.
Elpi Accumulate File derive_hook_for_mutual_wrapper_test.
Elpi Accumulate File derive_core_for_mutual_wrapper_test.
Elpi Accumulate lp:{{
  derivation (indt _) _ ff (derive "noop" (cl\ cl = []) true).

  main _ :-
    D = (parameter "A" maximal {{ Type }} a\
      (minductive "wleft" tt (arity {{ Type }}) l\
      (minductive "wright" tt (arity {{ Type }}) r\
        (mblock [
          [constructor "wleftK" (arity {{ lp:a -> lp:l }})],
          [constructor "wrightK" (arity {{ lp:a -> lp:r }})]
        ])))),
    get-option "module" "" ==> derive.decl+main "wleft" D.
}}.

Module WrapperMutualDeclaration.
  Elpi derive_mutual_wrapper_test.

  Check wright : Type.
  Check wleftK 0 : wleft.
  Check wrightK true : wright.
End WrapperMutualDeclaration.

Module Type MutualBase.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).
End MutualBase.

Module Type MutualMapExpected.
  Include MutualBase.
  Parameter tree_map : tree -> tree.
  Parameter forest_map : forest -> forest.
End MutualMapExpected.

Module Type MutualLensExpected.
  Include MutualBase.
  (* tree/forest are not records, so lens derives no Coq definitions. *)
End MutualLensExpected.

Module Type MutualLensLawsExpected.
  Include MutualLensExpected.
  (* No lenses means no lens-law constants. *)
End MutualLensLawsExpected.

Module Type MutualParam1Expected.
  Include MutualBase.
  Universe tree_reali_u forest_reali_u.
  Constraint Set < tree_reali_u.
  Constraint Set < forest_reali_u.
  Inductive is_tree : tree -> Type@{tree_reali_u} :=
  | is_node (f : forest) (Pf : is_forest f) : is_tree (node f)
  with is_forest : forest -> Type@{forest_reali_u} :=
  | is_empty : is_forest empty
  | is_cons (t : tree) (Pt : is_tree t)
      (f : forest) (Pf : is_forest f) : is_forest (cons t f).
  Parameter reali_is_tree : reali_db tree is_tree.
  Parameter reali_is_forest : reali_db forest is_forest.
  Parameter reali_is_tree_node : reali_db node is_node.
  Parameter reali_is_forest_empty : reali_db empty is_empty.
  Parameter reali_is_forest_cons : reali_db cons is_cons.
End MutualParam1Expected.

Module Type MutualParam1CongrExpected.
  Include MutualParam1Expected.
  Parameter congr_is_node :
    forall f (p1 p2 : is_forest f), p1 = p2 ->
      is_node f p1 = is_node f p2.
  Parameter congr_is_empty : is_empty = is_empty.
  Parameter congr_is_cons :
    forall t (p1 p2 : is_tree t), p1 = p2 ->
    forall f (q1 q2 : is_forest f), q1 = q2 ->
      is_cons t p1 f q1 = is_cons t p2 f q2.
End MutualParam1CongrExpected.

Module Type MutualParam1TrivialExpected.
  Include MutualParam1CongrExpected.
  Parameter is_tree_inhab : full tree is_tree.
  Parameter is_forest_inhab : full forest is_forest.
  Parameter is_tree_trivial : trivial tree is_tree.
  Parameter is_forest_trivial : trivial forest is_forest.
End MutualParam1TrivialExpected.

Module Type MutualParam1FunctorExpected.
  Include MutualParam1Expected.
  Parameter is_tree_functor : forall x : tree, is_tree x -> is_tree x.
  Parameter is_forest_functor : forall x : forest, is_forest x -> is_forest x.
End MutualParam1FunctorExpected.

Module Type MutualParam2Expected.
  Include MutualBase.
  Inductive tree_R : tree -> tree -> Set :=
  | node_R (f1 f2 : forest) (fR : forest_R f1 f2) :
      tree_R (node f1) (node f2)
  with forest_R : forest -> forest -> Set :=
  | empty_R : forest_R empty empty
  | cons_R (t1 t2 : tree) (tR : tree_R t1 t2)
      (f1 f2 : forest) (fR : forest_R f1 f2) :
      forest_R (cons t1 f1) (cons t2 f2).
  Parameter param_tree_R : param_db tree tree tree_R.
  Parameter param_forest_R : param_db forest forest forest_R.
  Parameter param_node_R : param_db node node node_R.
  Parameter param_empty_R : param_db empty empty empty_R.
  Parameter param_cons_R : param_db cons cons cons_R.
End MutualParam2Expected.

Module Type MutualInductionExpected.
  Include MutualParam1FunctorExpected.
  Parameter tree_induction :
    forall (P : tree -> Type) (Q : forest -> Type),
      (forall f (Pf : is_forest f), Q f -> P (node f)) ->
      Q empty ->
      (forall t (Pt : is_tree t), P t ->
       forall f (Pf : is_forest f), Q f -> Q (cons t f)) ->
      forall t, is_tree t -> P t.
End MutualInductionExpected.

Module Type MutualTagExpected.
  Include MutualBase.
  Parameter tree_tag : tree -> BinNums.positive.
  Parameter forest_tag : forest -> BinNums.positive.
End MutualTagExpected.

Module Type MutualFieldsExpected.
  Include MutualTagExpected.
  Universe box_tree_node_u.
  Constraint Set < box_tree_node_u.
  Record box_tree_node : Type@{box_tree_node_u} := Box_tree_node { Box_tree_node_0 : forest }.
  Parameter tree_fields_t : BinNums.positive -> Type.
  Parameter tree_fields : forall i : tree, tree_fields_t (tree_tag i).
  Parameter tree_construct :
    forall p : BinNums.positive, tree_fields_t p -> option tree.
  Parameter tree_constructP :
    forall i : tree, tree_construct (tree_tag i) (tree_fields i) = Some i.
  Parameter forest_fields_t : BinNums.positive -> Type.
  Parameter forest_fields : forall i : forest, forest_fields_t (forest_tag i).
  Parameter forest_construct :
    forall p : BinNums.positive, forest_fields_t p -> option forest.
  Parameter forest_constructP :
    forall i : forest, forest_construct (forest_tag i) (forest_fields i) = Some i.
End MutualFieldsExpected.

Module Type MutualEqbExpected.
  Include MutualFieldsExpected.
  Parameter tree_eqb_fields :
    (tree -> tree -> bool) ->
    forall x : BinNums.positive, tree_fields_t x -> tree_fields_t x -> bool.
  Parameter tree_eqb : tree -> tree -> bool.
  Parameter forest_eqb_fields :
    (forest -> forest -> bool) ->
    forall x : BinNums.positive, forest_fields_t x -> forest_fields_t x -> bool.
  Parameter forest_eqb : forest -> forest -> bool.
End MutualEqbExpected.

Module Type MutualEqbCorrectExpected.
  Include MutualEqbExpected.
  Parameter tree_eqb_correct : forall x : tree, eqb_correct_on tree_eqb x.
  Parameter forest_eqb_correct : forall x : forest, eqb_correct_on forest_eqb x.
  Parameter tree_eqb_refl : forall x : tree, eqb_refl_on tree_eqb x.
  Parameter forest_eqb_refl : forall x : forest, eqb_refl_on forest_eqb x.
End MutualEqbCorrectExpected.

Module Type MutualEqbOKExpected.
  Include MutualEqbCorrectExpected.
  Parameter tree_eqb_OK :
    forall x1 x2 : tree, reflect (x1 = x2) (tree_eqb x1 x2).
  Parameter tree_eqb_OK_sumbool : forall x y : tree, {x = y} + {x <> y}.
  Parameter forest_eqb_OK :
    forall x1 x2 : forest, reflect (x1 = x2) (forest_eqb x1 x2).
  Parameter forest_eqb_OK_sumbool : forall x y : forest, {x = y} + {x <> y}.
End MutualEqbOKExpected.

Module Type MutualIsKExpected.
  Include MutualBase.
  Parameter tree_isk_node : tree -> bool.
  Parameter forest_isk_empty : forest -> bool.
  Parameter forest_isk_cons : forest -> bool.
End MutualIsKExpected.

Module Type MutualProjKExpected.
  Include MutualBase.
  Parameter tree_getk_node1 : forest -> tree -> forest.
  Parameter forest_getk_cons1 : tree -> forest -> forest -> tree.
  Parameter forest_getk_cons2 : tree -> forest -> forest -> forest.
End MutualProjKExpected.

Module Type MutualBcongrExpected.
  Include MutualProjKExpected.
  Parameter tree_bcongr_node :
    forall x y b, reflect (x = y) b -> reflect (node x = node y) b.
  Parameter forest_bcongr_empty : reflect (empty = empty) true.
  Parameter forest_bcongr_cons :
    forall x y b, reflect (x = y) b ->
    forall x0 y0 b0, reflect (x0 = y0) b0 ->
      reflect (cons x x0 = cons y y0) (b && b0).
End MutualBcongrExpected.

Module Type ParametrizedMutualBase.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).
End ParametrizedMutualBase.

Module Type ParametrizedMutualMapExpected.
  Include ParametrizedMutualBase.
  Parameter ptree_map :
    forall A1 A2 : Type, (A1 -> A2) -> ptree A1 -> ptree A2.
  Parameter pforest_map :
    forall A1 A2 : Type, (A1 -> A2) -> pforest A1 -> pforest A2.
End ParametrizedMutualMapExpected.

Module Type ParametrizedMutualLensExpected.
  Include ParametrizedMutualBase.
  (* ptree/pforest are not records, so lens derives no Coq definitions. *)
End ParametrizedMutualLensExpected.

Module Type ParametrizedMutualLensLawsExpected.
  Include ParametrizedMutualLensExpected.
  (* No lenses means no lens-law constants. *)
End ParametrizedMutualLensLawsExpected.

Module Type ParametrizedMutualParam1Expected.
  Include ParametrizedMutualBase.
  Universe is_ptree_u0 is_ptree_u1 is_ptree_u2 is_ptree_u3 is_ptree_u4 is_ptree_u5 is_ptree_u6.
  Inductive is_ptree : forall A : Type, (A -> Type@{is_ptree_u0}) -> ptree A -> Type@{is_ptree_u1} :=
  | is_pnode : forall A (PA : A -> Type@{is_ptree_u2}) (x : A), PA x ->
      forall f : pforest A, is_pforest A PA f -> is_ptree A PA (@pnode A x f)
  with is_pforest : forall A : Type, (A -> Type@{is_ptree_u3}) -> pforest A -> Type@{is_ptree_u4} :=
  | is_pempty : forall A (PA : A -> Type@{is_ptree_u5}), is_pforest A PA (@pempty A)
  | is_pcons : forall A (PA : A -> Type@{is_ptree_u6}) (t : ptree A), is_ptree A PA t ->
      forall f : pforest A, is_pforest A PA f ->
      is_pforest A PA (@pcons A t f).
  Parameter reali_is_ptree : reali_db ptree is_ptree.
  Parameter reali_is_pforest : reali_db pforest is_pforest.
  Parameter reali_is_ptree_pnode : reali_db pnode is_pnode.
  Parameter reali_is_pforest_pempty : reali_db pempty is_pempty.
  Parameter reali_is_pforest_pcons : reali_db pcons is_pcons.
End ParametrizedMutualParam1Expected.

Module Type ParametrizedMutualParam1CongrExpected.
  Include ParametrizedMutualParam1Expected.
  Parameter congr_is_pnode :
    forall A PA x (p1 p2 : PA x), p1 = p2 ->
    forall f (q1 q2 : is_pforest A PA f), q1 = q2 ->
      is_pnode A PA x p1 f q1 = is_pnode A PA x p2 f q2.
  Parameter congr_is_pempty :
    forall A PA, is_pempty A PA = is_pempty A PA.
  Parameter congr_is_pcons :
    forall A PA t (p1 p2 : is_ptree A PA t), p1 = p2 ->
    forall f (q1 q2 : is_pforest A PA f), q1 = q2 ->
      is_pcons A PA t p1 f q1 = is_pcons A PA t p2 f q2.
End ParametrizedMutualParam1CongrExpected.

Module Type ParametrizedMutualParam1TrivialExpected.
  Include ParametrizedMutualParam1CongrExpected.
  Parameter is_ptree_inhab :
    forall A PA, full A PA -> full (ptree A) (is_ptree A PA).
  Parameter is_pforest_inhab :
    forall A PA, full A PA -> full (pforest A) (is_pforest A PA).
  Parameter is_ptree_trivial :
    forall A PA, trivial A PA -> trivial (ptree A) (is_ptree A PA).
  Parameter is_pforest_trivial :
    forall A PA, trivial A PA -> trivial (pforest A) (is_pforest A PA).
End ParametrizedMutualParam1TrivialExpected.

Module Type ParametrizedMutualParam1FunctorExpected.
  Include ParametrizedMutualParam1Expected.
  Parameter is_ptree_functor :
    forall A (P Q : A -> Type),
      (forall y : A, P y -> Q y) ->
      forall x : ptree A, is_ptree A P x -> is_ptree A Q x.
  Parameter is_pforest_functor :
    forall A (P Q : A -> Type),
      (forall y : A, P y -> Q y) ->
      forall x : pforest A, is_pforest A P x -> is_pforest A Q x.
End ParametrizedMutualParam1FunctorExpected.

Module Type ParametrizedMutualParam2Expected.
  Include ParametrizedMutualBase.
  Universe ptree_R_arg_u ptree_R_u0 ptree_R_u1.
  Inductive ptree_R : forall A1 A2 : Type@{ptree_R_arg_u}, (A1 -> A2 -> Type@{ptree_R_arg_u}) -> ptree A1 -> ptree A2 -> Type@{ptree_R_u0} :=
  | pnode_R : forall A1 A2 (A_R : A1 -> A2 -> Type@{ptree_R_arg_u}) (x1 : A1) (x2 : A2),
      A_R x1 x2 -> forall (f1 : pforest A1) (f2 : pforest A2),
      pforest_R A1 A2 A_R f1 f2 ->
      ptree_R A1 A2 A_R (@pnode A1 x1 f1) (@pnode A2 x2 f2)
  with pforest_R : forall A1 A2 : Type@{ptree_R_arg_u}, (A1 -> A2 -> Type@{ptree_R_arg_u}) -> pforest A1 -> pforest A2 -> Type@{ptree_R_u1} :=
  | pempty_R : forall A1 A2 (A_R : A1 -> A2 -> Type@{ptree_R_arg_u}),
      pforest_R A1 A2 A_R (@pempty A1) (@pempty A2)
  | pcons_R : forall A1 A2 (A_R : A1 -> A2 -> Type@{ptree_R_arg_u}) (t1 : ptree A1) (t2 : ptree A2),
      ptree_R A1 A2 A_R t1 t2 -> forall (f1 : pforest A1) (f2 : pforest A2),
      pforest_R A1 A2 A_R f1 f2 ->
      pforest_R A1 A2 A_R (@pcons A1 t1 f1) (@pcons A2 t2 f2).
  Parameter param_ptree_R : param_db ptree ptree ptree_R.
  Parameter param_pforest_R : param_db pforest pforest pforest_R.
  Parameter param_pnode_R : param_db pnode pnode pnode_R.
  Parameter param_pempty_R : param_db pempty pempty pempty_R.
  Parameter param_pcons_R : param_db pcons pcons pcons_R.
End ParametrizedMutualParam2Expected.

Module Type ParametrizedMutualInductionExpected.
  Include ParametrizedMutualParam1FunctorExpected.
  Parameter ptree_induction :
    forall (P : forall A : Type, (A -> Type) -> ptree A -> Type)
           (Q : forall A : Type, (A -> Type) -> pforest A -> Type),
      (forall A (PA : A -> Type) (x : A), PA x ->
       forall f, is_pforest A PA f -> Q A PA f -> P A PA (@pnode A x f)) ->
      (forall A (PA : A -> Type), Q A PA (@pempty A)) ->
      (forall A (PA : A -> Type) (t : ptree A), is_ptree A PA t -> P A PA t ->
       forall f, is_pforest A PA f -> Q A PA f -> Q A PA (@pcons A t f)) ->
      forall A (PA : A -> Type) t, is_ptree A PA t -> P A PA t.
End ParametrizedMutualInductionExpected.

Module Type ParametrizedMutualTagExpected.
  Include ParametrizedMutualBase.
  Parameter ptree_tag : forall A : Type, ptree A -> BinNums.positive.
  Parameter pforest_tag : forall A : Type, pforest A -> BinNums.positive.
End ParametrizedMutualTagExpected.

Module Type ParametrizedMutualFieldsExpected.
  Include ParametrizedMutualTagExpected.
  Universe box_ptree_pnode_u.
  Constraint Set < box_ptree_pnode_u.
  Record box_ptree_pnode (A : Type) : Type@{box_ptree_pnode_u} := Box_ptree_pnode {
    Box_ptree_pnode_0 : A;
    Box_ptree_pnode_1 : pforest A;
  }.
  Parameter ptree_fields_t : Type -> BinNums.positive -> Type.
  Parameter ptree_fields :
    forall (A : Type) (i : ptree A), ptree_fields_t A (ptree_tag A i).
  Parameter ptree_construct :
    forall A : Type, forall p : BinNums.positive,
      ptree_fields_t A p -> option (ptree A).
  Parameter ptree_constructP :
    forall (A : Type) (i : ptree A),
      ptree_construct A (ptree_tag A i) (ptree_fields A i) = Some i.
  Parameter pforest_fields_t : Type -> BinNums.positive -> Type.
  Parameter pforest_fields :
    forall (A : Type) (i : pforest A), pforest_fields_t A (pforest_tag A i).
  Parameter pforest_construct :
    forall A : Type, forall p : BinNums.positive,
      pforest_fields_t A p -> option (pforest A).
  Parameter pforest_constructP :
    forall (A : Type) (i : pforest A),
      pforest_construct A (pforest_tag A i) (pforest_fields A i) = Some i.
End ParametrizedMutualFieldsExpected.

Module Type ParametrizedMutualEqbExpected.
  Include ParametrizedMutualFieldsExpected.
  Parameter ptree_eqb_fields :
    forall A : Type, (A -> A -> bool) ->
      (ptree A -> ptree A -> bool) ->
      forall x : BinNums.positive,
        ptree_fields_t A x -> ptree_fields_t A x -> bool.
  Parameter ptree_eqb :
    forall A : Type, (A -> A -> bool) -> ptree A -> ptree A -> bool.
  Parameter pforest_eqb_fields :
    forall A : Type, (A -> A -> bool) ->
      (pforest A -> pforest A -> bool) ->
      forall x : BinNums.positive,
        pforest_fields_t A x -> pforest_fields_t A x -> bool.
  Parameter pforest_eqb :
    forall A : Type, (A -> A -> bool) -> pforest A -> pforest A -> bool.
End ParametrizedMutualEqbExpected.

Module Type ParametrizedMutualEqbCorrectExpected.
  Include ParametrizedMutualEqbExpected.
  Parameter ptree_eqb_correct :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_correct eqA ->
      forall x : ptree A, eqb_correct_on (ptree_eqb A eqA) x.
  Parameter ptree_eqb_refl :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_reflexive eqA ->
      forall x : ptree A, eqb_refl_on (ptree_eqb A eqA) x.
  Parameter pforest_eqb_correct :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_correct eqA ->
      forall x : pforest A, eqb_correct_on (pforest_eqb A eqA) x.
  Parameter pforest_eqb_refl :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_reflexive eqA ->
      forall x : pforest A, eqb_refl_on (pforest_eqb A eqA) x.
End ParametrizedMutualEqbCorrectExpected.

Module Type ParametrizedMutualEqbOKExpected.
  Include ParametrizedMutualEqbCorrectExpected.
  Parameter ptree_eqb_OK :
    forall (A : Type) (eqA : A -> A -> bool),
      (forall x1 x2 : A, reflect (x1 = x2) (eqA x1 x2)) ->
      forall x1 x2 : ptree A, reflect (x1 = x2) (ptree_eqb A eqA x1 x2).
  Parameter ptree_eqb_OK_sumbool :
    forall A : Type,
      (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
      forall x y : ptree A, {x = y} + {x <> y}.
  Parameter pforest_eqb_OK :
    forall (A : Type) (eqA : A -> A -> bool),
      (forall x1 x2 : A, reflect (x1 = x2) (eqA x1 x2)) ->
      forall x1 x2 : pforest A, reflect (x1 = x2) (pforest_eqb A eqA x1 x2).
  Parameter pforest_eqb_OK_sumbool :
    forall A : Type,
      (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
      forall x y : pforest A, {x = y} + {x <> y}.
End ParametrizedMutualEqbOKExpected.

Module Type ParametrizedMutualIsKExpected.
  Include ParametrizedMutualBase.
  Parameter ptree_isk_pnode : forall A : Type, ptree A -> bool.
  Parameter pforest_isk_pempty : forall A : Type, pforest A -> bool.
  Parameter pforest_isk_pcons : forall A : Type, pforest A -> bool.
End ParametrizedMutualIsKExpected.

Module Type ParametrizedMutualProjKExpected.
  Include ParametrizedMutualBase.
  Parameter ptree_getk_pnode1 : forall A : Type, A -> pforest A -> ptree A -> A.
  Parameter ptree_getk_pnode2 : forall A : Type, A -> pforest A -> ptree A -> pforest A.
  Parameter pforest_getk_pcons1 :
    forall A : Type, ptree A -> pforest A -> pforest A -> ptree A.
  Parameter pforest_getk_pcons2 :
    forall A : Type, ptree A -> pforest A -> pforest A -> pforest A.
End ParametrizedMutualProjKExpected.

Module Type ParametrizedMutualBcongrExpected.
  Include ParametrizedMutualProjKExpected.
  Parameter ptree_bcongr_pnode :
    forall A x y b, reflect (x = y) b ->
    forall x0 y0 b0, reflect (x0 = y0) b0 ->
      reflect (pnode A x x0 = pnode A y y0) (b && b0).
  Parameter pforest_bcongr_pempty : forall A : Type, reflect (pempty A = pempty A) true.
  Parameter pforest_bcongr_pcons :
    forall A x y b, reflect (x = y) b ->
    forall x0 y0 b0, reflect (x0 = y0) b0 ->
      reflect (pcons A x x0 = pcons A y y0) (b && b0).
End ParametrizedMutualBcongrExpected.

Module Type TripleMutualBase.
  Inductive alpha : Type :=
  | alpha0
  | alpha1 (b : beta)
  with beta : Type :=
  | beta0
  | beta1 (g : gamma)
  with gamma : Type :=
  | gamma0
  | gamma1 (a : alpha) (b : beta).
End TripleMutualBase.

Module Type TripleMutualMapExpected.
  Include TripleMutualBase.
  Parameter alpha_map : alpha -> alpha.
  Parameter beta_map : beta -> beta.
  Parameter gamma_map : gamma -> gamma.
End TripleMutualMapExpected.

Module Type TripleMutualEqbExpected.
  Include TripleMutualBase.
  Parameter alpha_tag : alpha -> BinNums.positive.
  Parameter beta_tag : beta -> BinNums.positive.
  Parameter gamma_tag : gamma -> BinNums.positive.
  Parameter alpha_fields_t : BinNums.positive -> Type.
  Parameter beta_fields_t : BinNums.positive -> Type.
  Parameter gamma_fields_t : BinNums.positive -> Type.
  Parameter alpha_fields : forall i : alpha, alpha_fields_t (alpha_tag i).
  Parameter beta_fields : forall i : beta, beta_fields_t (beta_tag i).
  Parameter gamma_fields : forall i : gamma, gamma_fields_t (gamma_tag i).
  Parameter alpha_eqb_fields :
    (alpha -> alpha -> bool) ->
    forall x : BinNums.positive, alpha_fields_t x -> alpha_fields_t x -> bool.
  Parameter beta_eqb_fields :
    (beta -> beta -> bool) ->
    forall x : BinNums.positive, beta_fields_t x -> beta_fields_t x -> bool.
  Parameter gamma_eqb_fields :
    (gamma -> gamma -> bool) ->
    forall x : BinNums.positive, gamma_fields_t x -> gamma_fields_t x -> bool.
  Parameter alpha_eqb : alpha -> alpha -> bool.
  Parameter beta_eqb : beta -> beta -> bool.
  Parameter gamma_eqb : gamma -> gamma -> bool.
End TripleMutualEqbExpected.

Module Type TripleMutualEqbOKExpected.
  Include TripleMutualEqbExpected.
  Parameter alpha_eqb_correct : forall x : alpha, eqb_correct_on alpha_eqb x.
  Parameter beta_eqb_correct : forall x : beta, eqb_correct_on beta_eqb x.
  Parameter gamma_eqb_correct : forall x : gamma, eqb_correct_on gamma_eqb x.
  Parameter alpha_eqb_refl : forall x : alpha, eqb_refl_on alpha_eqb x.
  Parameter beta_eqb_refl : forall x : beta, eqb_refl_on beta_eqb x.
  Parameter gamma_eqb_refl : forall x : gamma, eqb_refl_on gamma_eqb x.
  Parameter alpha_eqb_OK :
    forall x1 x2 : alpha, reflect (x1 = x2) (alpha_eqb x1 x2).
  Parameter beta_eqb_OK :
    forall x1 x2 : beta, reflect (x1 = x2) (beta_eqb x1 x2).
  Parameter gamma_eqb_OK :
    forall x1 x2 : gamma, reflect (x1 = x2) (gamma_eqb x1 x2).
  Parameter alpha_eqb_OK_sumbool : forall x y : alpha, {x = y} + {x <> y}.
  Parameter beta_eqb_OK_sumbool : forall x y : beta, {x = y} + {x <> y}.
  Parameter gamma_eqb_OK_sumbool : forall x y : gamma, {x = y} + {x <> y}.
End TripleMutualEqbOKExpected.

Module Type ParametrizedTripleMutualBase.
  Inductive palpha (A : Type) : Type :=
  | palpha0
  | palpha1 (x : A) (b : pbeta A)
  with pbeta (A : Type) : Type :=
  | pbeta0
  | pbeta1 (g : pgamma A)
  with pgamma (A : Type) : Type :=
  | pgamma0
  | pgamma1 (a : palpha A) (b : pbeta A).
End ParametrizedTripleMutualBase.

Module Type ParametrizedTripleMutualEqbExpected.
  Include ParametrizedTripleMutualBase.
  Parameter palpha_eqb :
    forall A : Type, (A -> A -> bool) -> palpha A -> palpha A -> bool.
  Parameter pbeta_eqb :
    forall A : Type, (A -> A -> bool) -> pbeta A -> pbeta A -> bool.
  Parameter pgamma_eqb :
    forall A : Type, (A -> A -> bool) -> pgamma A -> pgamma A -> bool.
End ParametrizedTripleMutualEqbExpected.

Module Type ParametrizedTripleMutualEqbOKExpected.
  Include ParametrizedTripleMutualEqbExpected.
  Parameter palpha_eqb_correct :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_correct eqA ->
      forall x : palpha A, eqb_correct_on (palpha_eqb A eqA) x.
  Parameter pbeta_eqb_correct :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_correct eqA ->
      forall x : pbeta A, eqb_correct_on (pbeta_eqb A eqA) x.
  Parameter pgamma_eqb_correct :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_correct eqA ->
      forall x : pgamma A, eqb_correct_on (pgamma_eqb A eqA) x.
  Parameter palpha_eqb_refl :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_reflexive eqA ->
      forall x : palpha A, eqb_refl_on (palpha_eqb A eqA) x.
  Parameter pbeta_eqb_refl :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_reflexive eqA ->
      forall x : pbeta A, eqb_refl_on (pbeta_eqb A eqA) x.
  Parameter pgamma_eqb_refl :
    forall (A : Type) (eqA : A -> A -> bool),
      eqb_reflexive eqA ->
      forall x : pgamma A, eqb_refl_on (pgamma_eqb A eqA) x.
  Parameter palpha_eqb_OK :
    forall (A : Type) (eqA : A -> A -> bool),
      (forall x1 x2 : A, reflect (x1 = x2) (eqA x1 x2)) ->
      forall x1 x2 : palpha A, reflect (x1 = x2) (palpha_eqb A eqA x1 x2).
  Parameter pbeta_eqb_OK :
    forall (A : Type) (eqA : A -> A -> bool),
      (forall x1 x2 : A, reflect (x1 = x2) (eqA x1 x2)) ->
      forall x1 x2 : pbeta A, reflect (x1 = x2) (pbeta_eqb A eqA x1 x2).
  Parameter pgamma_eqb_OK :
    forall (A : Type) (eqA : A -> A -> bool),
      (forall x1 x2 : A, reflect (x1 = x2) (eqA x1 x2)) ->
      forall x1 x2 : pgamma A, reflect (x1 = x2) (pgamma_eqb A eqA x1 x2).
  Parameter palpha_eqb_OK_sumbool :
    forall A : Type,
      (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
      forall x y : palpha A, {x = y} + {x <> y}.
  Parameter pbeta_eqb_OK_sumbool :
    forall A : Type,
      (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
      forall x y : pbeta A, {x = y} + {x <> y}.
  Parameter pgamma_eqb_OK_sumbool :
    forall A : Type,
      (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
      forall x y : pgamma A, {x = y} + {x <> y}.
End ParametrizedTripleMutualEqbOKExpected.

Module MutualMap <: MutualMapExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(map)] derive tree.

  Example tree_map_computes :
    tree_map (node (cons (node empty) empty)) = node (cons (node empty) empty).
  Proof. vm_compute. reflexivity. Qed.

  Example forest_map_computes :
    forest_map (cons (node empty) empty) = cons (node empty) empty.
  Proof. vm_compute. reflexivity. Qed.
End MutualMap.

Module MutualLens <: MutualLensExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(lens)] derive tree.
End MutualLens.

Module MutualLensLaws <: MutualLensLawsExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(lens_laws)] derive tree.
End MutualLensLaws.

Module MutualParam1 <: MutualParam1Expected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1)] derive tree.

  Example is_tree_match_computes :
    (match is_node empty is_empty with
     | is_node f _ => node f
     end) = node empty.
  Proof. vm_compute. reflexivity. Qed.

  Example is_forest_match_computes :
    (match is_cons (node empty) (is_node empty is_empty) empty is_empty with
     | is_empty => empty
     | is_cons t _ f _ => cons t f
     end) = cons (node empty) empty.
  Proof. vm_compute. reflexivity. Qed.
End MutualParam1.

Module MutualParam1Congr <: MutualParam1CongrExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1_congr)] derive tree.

  Example congr_is_node_computes :
    congr_is_node empty is_empty is_empty eq_refl = eq_refl.
  Proof. vm_compute. reflexivity. Qed.

  Example congr_is_cons_computes :
    congr_is_cons (node empty) (is_node empty is_empty) (is_node empty is_empty)
      eq_refl empty is_empty is_empty eq_refl = eq_refl.
  Proof. vm_compute. reflexivity. Qed.
End MutualParam1Congr.

Module MutualParam1Trivial <: MutualParam1TrivialExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1_trivial)] derive tree.

  Example is_tree_inhab_computes :
    is_tree_inhab (node empty) = is_node empty is_empty.
  Proof. vm_compute. reflexivity. Qed.

  Example is_forest_inhab_computes :
    is_forest_inhab (cons (node empty) empty) =
    is_cons (node empty) (is_node empty is_empty) empty is_empty.
  Proof. vm_compute. reflexivity. Qed.

  Example is_tree_trivial_witness_computes :
    projT1 (is_tree_trivial (node empty)) = is_node empty is_empty.
  Proof. vm_compute. reflexivity. Qed.

  Example is_forest_trivial_witness_computes :
    projT1 (is_forest_trivial (cons (node empty) empty)) =
    is_cons (node empty) (is_node empty is_empty) empty is_empty.
  Proof. vm_compute. reflexivity. Qed.
End MutualParam1Trivial.

Module MutualParam1Functor <: MutualParam1FunctorExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1_functor)] derive tree.

  Example is_tree_functor_computes :
    is_tree_functor (node empty) (is_node empty is_empty) = is_node empty is_empty.
  Proof. vm_compute. reflexivity. Qed.

  Example is_forest_functor_computes :
    is_forest_functor (cons (node empty) empty)
      (is_cons (node empty) (is_node empty is_empty) empty is_empty) =
    is_cons (node empty) (is_node empty is_empty) empty is_empty.
  Proof. vm_compute. reflexivity. Qed.
End MutualParam1Functor.

Module MutualParam2 <: MutualParam2Expected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param2)] derive tree.

  Example tree_R_match_computes :
    (match node_R empty empty empty_R with
     | node_R f1 _ _ => node f1
     end) = node empty.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_R_match_computes :
    (match cons_R (node empty) (node empty) (node_R empty empty empty_R)
             empty empty empty_R with
     | empty_R => empty
     | cons_R t1 _ _ f1 _ _ => cons t1 f1
     end) = cons (node empty) empty.
  Proof. vm_compute. reflexivity. Qed.
End MutualParam2.

Module MutualInduction <: MutualInductionExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(induction)] derive tree.

  Example tree_induction_computes :
    tree_induction
      (fun _ => nat) (fun _ => nat)
      (fun _ _ q => S q)
      0
      (fun _ _ pt _ _ qf => S (pt + qf))
      (node empty) (is_node empty is_empty) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_induction_computes :
    forest_induction
      (fun _ => nat) (fun _ => nat)
      (fun _ _ q => S q)
      0
      (fun _ _ pt _ _ qf => S (pt + qf))
      (cons (node empty) empty)
      (is_cons (node empty) (is_node empty is_empty) empty is_empty) = 2.
  Proof. vm_compute. reflexivity. Qed.
End MutualInduction.

Module MutualTag <: MutualTagExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(tag)] derive tree.

  Example tree_tag_computes : tree_tag (node empty) = xH.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_tag_empty_computes : forest_tag empty = xH.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_tag_cons_computes : forest_tag (cons (node empty) empty) = xO xH.
  Proof. vm_compute. reflexivity. Qed.
End MutualTag.

Module MutualFields <: MutualFieldsExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(fields)] derive tree.

  Example tree_construct_computes :
    tree_construct (tree_tag (node empty)) (tree_fields (node empty)) = Some (node empty).
  Proof. vm_compute. reflexivity. Qed.

  Example forest_construct_computes :
    forest_construct (forest_tag (cons (node empty) empty))
      (forest_fields (cons (node empty) empty)) = Some (cons (node empty) empty).
  Proof. vm_compute. reflexivity. Qed.
End MutualFields.

Module MutualEqb <: MutualEqbExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(eqb)] derive tree.

  Example tree_eqb_computes_equal :
    tree_eqb (node empty) (node empty) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example tree_eqb_computes_different :
    tree_eqb (node empty) (node (cons (node empty) empty)) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_eqb_computes_equal :
    forest_eqb (cons (node empty) empty) (cons (node empty) empty) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_eqb_computes_different :
    forest_eqb empty (cons (node empty) empty) = false.
  Proof. vm_compute. reflexivity. Qed.
End MutualEqb.

Module NonRecursiveMutualEqb.
  Inductive color : Type :=
  | red
  | blue
  with shape : Type :=
  | circle
  | square.

  #[only(eqb)] derive color.

  Example color_eqb_computes_equal : color_eqb red red = true.
  Proof. vm_compute. reflexivity. Qed.

  Example color_eqb_computes_different : color_eqb red blue = false.
  Proof. vm_compute. reflexivity. Qed.

  Example shape_eqb_computes_equal : shape_eqb circle circle = true.
  Proof. vm_compute. reflexivity. Qed.

  Example shape_eqb_computes_different : shape_eqb circle square = false.
  Proof. vm_compute. reflexivity. Qed.
End NonRecursiveMutualEqb.

Module NonRecursiveMutualParam1.
  Inductive color : Type :=
  | red
  | blue
  with shape : Type :=
  | circle
  | square.

  #[only(param1)] derive color.

  Check is_color : color -> Type.
  Check is_shape : shape -> Type.
  Check is_red : is_color red.
  Check is_circle : is_shape circle.
End NonRecursiveMutualParam1.

Module NonRecursiveMutualParam2.
  Inductive color : Type :=
  | red
  | blue
  with shape : Type :=
  | circle
  | square.

  #[only(param2)] derive color.

  Check color_R : color -> color -> Set.
  Check shape_R : shape -> shape -> Set.
  Check red_R : color_R red red.
  Check circle_R : shape_R circle circle.
End NonRecursiveMutualParam2.

Module ValueParamMutualEqbUnsupported.
  Inductive a (n : nat) : Type :=
  | ak (b0 : b n)
  with b (n : nat) : Type :=
  | bk (a0 : a n).

  Fail #[only(eqb)] derive a.
End ValueParamMutualEqbUnsupported.

Module MutualEqbCorrect <: MutualEqbCorrectExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(eqbcorrect)] derive tree.

  Ltac transparent_function c :=
    let t := eval cbv delta [c] in c in
    lazymatch t with
    | fun _ => _ => idtac
    | _ => fail 1 "expected" c "to unfold to a function"
    end.

  Example tree_eqb_refl_is_transparent : True.
  Proof. transparent_function tree_eqb_refl. exact I. Qed.

  Example forest_eqb_refl_is_transparent : True.
  Proof. transparent_function forest_eqb_refl. exact I. Qed.

  Example tree_eqb_correct_is_transparent : True.
  Proof. transparent_function tree_eqb_correct. exact I. Qed.

  Example forest_eqb_correct_is_transparent : True.
  Proof. transparent_function forest_eqb_correct. exact I. Qed.
End MutualEqbCorrect.

Module MutualEqbOK <: MutualEqbOKExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(eqbOK)] derive tree.
End MutualEqbOK.

Module MutualIsK <: MutualIsKExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(isK)] derive tree.

  Example tree_isk_node_computes : tree_isk_node (node empty) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_isk_empty_computes : forest_isk_empty empty = true.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_isk_cons_computes : forest_isk_cons (cons (node empty) empty) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_isk_empty_rejects_cons : forest_isk_empty (cons (node empty) empty) = false.
  Proof. vm_compute. reflexivity. Qed.
End MutualIsK.

Module MutualProjK <: MutualProjKExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(projK)] derive tree.

  Example tree_getk_node1_computes :
    tree_getk_node1 empty (node (cons (node empty) empty)) = cons (node empty) empty.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_getk_cons1_computes :
    forest_getk_cons1 (node empty) empty (cons (node empty) empty) = node empty.
  Proof. vm_compute. reflexivity. Qed.

  Example forest_getk_cons2_computes :
    forest_getk_cons2 (node empty) empty (cons (node empty) (cons (node empty) empty)) =
    cons (node empty) empty.
  Proof. vm_compute. reflexivity. Qed.
End MutualProjK.

Module MutualBcongr <: MutualBcongrExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(bcongr)] derive tree.

  Example tree_bcongr_node_works :
    reflect (node empty = node empty) true.
  Proof. exact (tree_bcongr_node empty empty true (ReflectT _ eq_refl)). Qed.

  Example forest_bcongr_cons_works :
    reflect (cons (node empty) empty = cons (node empty) empty) true.
  Proof.
    exact (forest_bcongr_cons (node empty) (node empty) true (ReflectT _ eq_refl)
             empty empty true (ReflectT _ eq_refl)).
  Qed.
End MutualBcongr.

Module ParametrizedMutualMap <: ParametrizedMutualMapExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(map)] derive ptree.

  Example ptree_map_computes :
    ptree_map nat bool Nat.even (pnode nat 2 (pempty nat)) =
    pnode bool true (pempty bool).
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_map_computes :
    pforest_map nat bool Nat.even
      (pcons nat (pnode nat 3 (pempty nat)) (pempty nat)) =
    pcons bool (pnode bool false (pempty bool)) (pempty bool).
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualMap.

Module ParametrizedMutualLens <: ParametrizedMutualLensExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(lens)] derive ptree.
End ParametrizedMutualLens.

Module ParametrizedMutualLensLaws <: ParametrizedMutualLensLawsExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(lens_laws)] derive ptree.
End ParametrizedMutualLensLaws.

Module ParametrizedMutualParam1 <: ParametrizedMutualParam1Expected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param1)] derive ptree.

  Example is_ptree_match_computes :
    (match is_pnode nat (fun _ => unit) 2 tt (pempty nat)
             (is_pempty nat (fun _ => unit))
       in is_ptree A _ _ return ptree A with
     | is_pnode A _ x _ f _ => pnode A x f
     end) = pnode nat 2 (pempty nat).
  Proof. vm_compute. reflexivity. Qed.

  Example is_pforest_match_computes :
    (match is_pcons nat (fun _ => unit) (pnode nat 2 (pempty nat))
             (is_pnode nat (fun _ => unit) 2 tt (pempty nat)
               (is_pempty nat (fun _ => unit)))
             (pempty nat) (is_pempty nat (fun _ => unit))
       in is_pforest A _ _ return pforest A with
     | is_pempty A _ => pempty A
     | is_pcons A _ t _ f _ => pcons A t f
     end) = pcons nat (pnode nat 2 (pempty nat)) (pempty nat).
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualParam1.

Module ParametrizedMutualParam1Congr <: ParametrizedMutualParam1CongrExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param1_congr)] derive ptree.

  Example congr_is_pnode_computes :
    congr_is_pnode nat (fun _ => unit) 2 tt tt eq_refl
      (pempty nat) (is_pempty nat (fun _ => unit))
      (is_pempty nat (fun _ => unit)) eq_refl = eq_refl.
  Proof. vm_compute. reflexivity. Qed.

  Example congr_is_pcons_computes :
    congr_is_pcons nat (fun _ => unit) (pnode nat 2 (pempty nat))
      (is_pnode nat (fun _ => unit) 2 tt (pempty nat)
        (is_pempty nat (fun _ => unit)))
      (is_pnode nat (fun _ => unit) 2 tt (pempty nat)
        (is_pempty nat (fun _ => unit))) eq_refl
      (pempty nat) (is_pempty nat (fun _ => unit))
      (is_pempty nat (fun _ => unit)) eq_refl = eq_refl.
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualParam1Congr.

Module ParametrizedMutualParam1TrivialUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  Fail #[only(param1_trivial)] derive ptree.
End ParametrizedMutualParam1TrivialUnsupported.

Module ParametrizedMutualParam1FunctorUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  Fail #[only(param1_functor)] derive ptree.
End ParametrizedMutualParam1FunctorUnsupported.

Module ParametrizedMutualParam2 <: ParametrizedMutualParam2Expected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param2)] derive ptree.

  Definition nat_eq_relation := fun x y : nat => x = y.
  Definition pnode_R_example :=
    pnode_R nat nat nat_eq_relation 2 2 eq_refl
      (pempty nat) (pempty nat) (pempty_R nat nat nat_eq_relation).

  Example ptree_R_match_computes :
    (match pnode_R_example in ptree_R A1 _ _ _ _ return ptree A1 with
     | pnode_R A1 _ _ x1 _ _ f1 _ _ => pnode A1 x1 f1
     end) = pnode nat 2 (pempty nat).
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_R_match_computes :
    (match pcons_R nat nat nat_eq_relation
             (pnode nat 2 (pempty nat)) (pnode nat 2 (pempty nat)) pnode_R_example
             (pempty nat) (pempty nat) (pempty_R nat nat nat_eq_relation)
       in pforest_R A1 _ _ _ _ return pforest A1 with
     | pempty_R A1 _ _ => pempty A1
     | pcons_R A1 _ _ t1 _ _ f1 _ _ => pcons A1 t1 f1
     end) = pcons nat (pnode nat 2 (pempty nat)) (pempty nat).
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualParam2.

Module ParametrizedMutualInductionUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  Fail #[only(induction)] derive ptree.
End ParametrizedMutualInductionUnsupported.

Module ParametrizedMutualTag <: ParametrizedMutualTagExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(tag)] derive ptree.

  Example ptree_tag_computes :
    ptree_tag nat (pnode nat 2 (pempty nat)) = xH.
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_tag_empty_computes : pforest_tag nat (pempty nat) = xH.
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_tag_cons_computes :
    pforest_tag nat (pcons nat (pnode nat 2 (pempty nat)) (pempty nat)) = xO xH.
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualTag.

Module ParametrizedMutualFields <: ParametrizedMutualFieldsExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(fields)] derive ptree.

  Example ptree_construct_computes :
    ptree_construct nat (ptree_tag nat (pnode nat 2 (pempty nat)))
      (ptree_fields nat (pnode nat 2 (pempty nat))) = Some (pnode nat 2 (pempty nat)).
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_construct_computes :
    pforest_construct nat
      (pforest_tag nat (pcons nat (pnode nat 2 (pempty nat)) (pempty nat)))
      (pforest_fields nat (pcons nat (pnode nat 2 (pempty nat)) (pempty nat))) =
    Some (pcons nat (pnode nat 2 (pempty nat)) (pempty nat)).
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualFields.

Module ParametrizedMutualEqb <: ParametrizedMutualEqbExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(eqb)] derive ptree.

  Example ptree_eqb_computes_equal :
    ptree_eqb nat Nat.eqb (pnode nat 2 (pempty nat)) (pnode nat 2 (pempty nat)) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example ptree_eqb_computes_different :
    ptree_eqb nat Nat.eqb (pnode nat 2 (pempty nat)) (pnode nat 3 (pempty nat)) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_eqb_computes_equal :
    pforest_eqb nat Nat.eqb
      (pcons nat (pnode nat 2 (pempty nat)) (pempty nat))
      (pcons nat (pnode nat 2 (pempty nat)) (pempty nat)) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_eqb_computes_different :
    pforest_eqb nat Nat.eqb
      (pcons nat (pnode nat 2 (pempty nat)) (pempty nat))
      (pcons nat (pnode nat 3 (pempty nat)) (pempty nat)) = false.
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualEqb.

Module ParametrizedMutualEqbCorrectUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  Fail #[only(eqbcorrect)] derive ptree.
End ParametrizedMutualEqbCorrectUnsupported.

Module ParametrizedMutualEqbOKUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  Fail #[only(eqbOK)] derive ptree.
End ParametrizedMutualEqbOKUnsupported.

Module ParametrizedMutualIsK <: ParametrizedMutualIsKExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(isK)] derive ptree.

  Example ptree_isk_pnode_computes :
    ptree_isk_pnode nat (pnode nat 2 (pempty nat)) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_isk_pempty_computes : pforest_isk_pempty nat (pempty nat) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_isk_pcons_computes :
    pforest_isk_pcons nat (pcons nat (pnode nat 2 (pempty nat)) (pempty nat)) = true.
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualIsK.

Module ParametrizedMutualProjK <: ParametrizedMutualProjKExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(projK)] derive ptree.

  Example ptree_getk_pnode1_computes :
    ptree_getk_pnode1 nat 0 (pempty nat) (pnode nat 2 (pempty nat)) = 2.
  Proof. vm_compute. reflexivity. Qed.

  Example ptree_getk_pnode2_computes :
    ptree_getk_pnode2 nat 0 (pempty nat) (pnode nat 2 (pcons nat (pnode nat 3 (pempty nat)) (pempty nat))) =
    pcons nat (pnode nat 3 (pempty nat)) (pempty nat).
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_getk_pcons1_computes :
    pforest_getk_pcons1 nat (pnode nat 0 (pempty nat)) (pempty nat)
      (pcons nat (pnode nat 2 (pempty nat)) (pempty nat)) = pnode nat 2 (pempty nat).
  Proof. vm_compute. reflexivity. Qed.

  Example pforest_getk_pcons2_computes :
    pforest_getk_pcons2 nat (pnode nat 0 (pempty nat)) (pempty nat)
      (pcons nat (pnode nat 2 (pempty nat)) (pcons nat (pnode nat 3 (pempty nat)) (pempty nat))) =
    pcons nat (pnode nat 3 (pempty nat)) (pempty nat).
  Proof. vm_compute. reflexivity. Qed.
End ParametrizedMutualProjK.

Module ParametrizedMutualBcongr <: ParametrizedMutualBcongrExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(bcongr)] derive ptree.

  Example ptree_bcongr_pnode_works :
    reflect (pnode nat 2 (pempty nat) = pnode nat 2 (pempty nat)) true.
  Proof.
    exact (ptree_bcongr_pnode nat 2 2 true (ReflectT _ eq_refl)
             (pempty nat) (pempty nat) true (ReflectT _ eq_refl)).
  Qed.

  Example pforest_bcongr_pcons_works :
    reflect (pcons nat (pnode nat 2 (pempty nat)) (pempty nat) =
             pcons nat (pnode nat 2 (pempty nat)) (pempty nat)) true.
  Proof.
    exact (pforest_bcongr_pcons nat
             (pnode nat 2 (pempty nat)) (pnode nat 2 (pempty nat)) true (ReflectT _ eq_refl)
             (pempty nat) (pempty nat) true (ReflectT _ eq_refl)).
  Qed.
End ParametrizedMutualBcongr.

Module TripleMutualMapFromGamma <: TripleMutualMapExpected.
  Inductive alpha : Type :=
  | alpha0
  | alpha1 (b : beta)
  with beta : Type :=
  | beta0
  | beta1 (g : gamma)
  with gamma : Type :=
  | gamma0
  | gamma1 (a : alpha) (b : beta).

  #[only(map)] derive gamma.

  Example alpha_map_computes :
    alpha_map (alpha1 (beta1 gamma0)) = alpha1 (beta1 gamma0).
  Proof. vm_compute. reflexivity. Qed.

  Example beta_map_computes : beta_map (beta1 gamma0) = beta1 gamma0.
  Proof. vm_compute. reflexivity. Qed.

  Example gamma_map_computes :
    gamma_map (gamma1 (alpha1 beta0) beta0) = gamma1 (alpha1 beta0) beta0.
  Proof. vm_compute. reflexivity. Qed.
End TripleMutualMapFromGamma.

Module TripleMutualEqbFromAlpha <: TripleMutualEqbExpected.
  Inductive alpha : Type :=
  | alpha0
  | alpha1 (b : beta)
  with beta : Type :=
  | beta0
  | beta1 (g : gamma)
  with gamma : Type :=
  | gamma0
  | gamma1 (a : alpha) (b : beta).

  #[only(eqb)] derive alpha.
End TripleMutualEqbFromAlpha.

Module TripleMutualEqbFromBeta <: TripleMutualEqbExpected.
  Inductive alpha : Type :=
  | alpha0
  | alpha1 (b : beta)
  with beta : Type :=
  | beta0
  | beta1 (g : gamma)
  with gamma : Type :=
  | gamma0
  | gamma1 (a : alpha) (b : beta).

  #[only(eqb)] derive beta.
End TripleMutualEqbFromBeta.

Module TripleMutualEqbFromGamma <: TripleMutualEqbExpected.
  Inductive alpha : Type :=
  | alpha0
  | alpha1 (b : beta)
  with beta : Type :=
  | beta0
  | beta1 (g : gamma)
  with gamma : Type :=
  | gamma0
  | gamma1 (a : alpha) (b : beta).

  #[only(eqb)] derive gamma.
End TripleMutualEqbFromGamma.

Module TripleMutualEqbOKFromBeta <: TripleMutualEqbOKExpected.
  Inductive alpha : Type :=
  | alpha0
  | alpha1 (b : beta)
  with beta : Type :=
  | beta0
  | beta1 (g : gamma)
  with gamma : Type :=
  | gamma0
  | gamma1 (a : alpha) (b : beta).

  #[only(eqbOK)] derive beta.

  Example alpha_eqb_computes_equal : alpha_eqb (alpha1 beta0) (alpha1 beta0) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example alpha_eqb_computes_different : alpha_eqb alpha0 (alpha1 beta0) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example beta_eqb_computes_equal : beta_eqb (beta1 gamma0) (beta1 gamma0) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example gamma_eqb_computes_different :
    gamma_eqb (gamma1 alpha0 beta0) (gamma1 (alpha1 beta0) beta0) = false.
  Proof. vm_compute. reflexivity. Qed.
End TripleMutualEqbOKFromBeta.

Module ParametrizedTripleMutualEqbOKFromBetaUnsupported.
  Inductive palpha (A : Type) : Type :=
  | palpha0
  | palpha1 (x : A) (b : pbeta A)
  with pbeta (A : Type) : Type :=
  | pbeta0
  | pbeta1 (g : pgamma A)
  with pgamma (A : Type) : Type :=
  | pgamma0
  | pgamma1 (a : palpha A) (b : pbeta A).

  Fail #[only(eqbOK)] derive pbeta.
End ParametrizedTripleMutualEqbOKFromBetaUnsupported.
