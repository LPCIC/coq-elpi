(* This is the same derivation set exported by derive.std, kept explicit so
   each standard derivation is tested independently.  Each derive call below
   lives in its own module and is checked against a signature documenting the
   Coq definitions that derivation is expected to add. *)
From Corelib Require Import BinNums ssrbool.
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
  derive.eqbOK.

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
End MutualTagExpected.

Module Type MutualFieldsExpected.
  Include MutualTagExpected.
  Record box_tree_node : Type := Box_tree_node { Box_tree_node_0 : forest }.
  Parameter tree_fields_t : BinNums.positive -> Type.
  Parameter tree_fields : forall i : tree, tree_fields_t (tree_tag i).
  Parameter tree_construct :
    forall p : BinNums.positive, tree_fields_t p -> option tree.
  Parameter tree_constructP :
    forall i : tree, tree_construct (tree_tag i) (tree_fields i) = Some i.
End MutualFieldsExpected.

Module Type MutualEqbExpected.
  Include MutualFieldsExpected.
  Parameter tree_eqb_fields :
    (tree -> tree -> bool) ->
    forall x : BinNums.positive, tree_fields_t x -> tree_fields_t x -> bool.
  Parameter tree_eqb : tree -> tree -> bool.
End MutualEqbExpected.

Module Type MutualEqbCorrectExpected.
  Include MutualEqbExpected.
  Parameter tree_eqb_correct : forall x : tree, eqb_correct_on tree_eqb x.
  Parameter tree_eqb_refl : forall x : tree, eqb_refl_on tree_eqb x.
End MutualEqbCorrectExpected.

Module Type MutualEqbOKExpected.
  Include MutualEqbCorrectExpected.
  Parameter tree_eqb_OK :
    forall x1 x2 : tree, reflect (x1 = x2) (tree_eqb x1 x2).
  Parameter tree_eqb_OK_sumbool : forall x y : tree, {x = y} + {x <> y}.
End MutualEqbOKExpected.

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
  Inductive is_ptree (A : Type) (PA : A -> Type) : ptree A -> Type :=
  | is_pnode (x : A) (Px : PA x) (f : pforest A)
      (Pf : is_pforest A PA f) : is_ptree A PA (@pnode A x f)
  with is_pforest (A : Type) (PA : A -> Type) : pforest A -> Type :=
  | is_pempty : is_pforest A PA (@pempty A)
  | is_pcons (t : ptree A) (Pt : is_ptree A PA t)
      (f : pforest A) (Pf : is_pforest A PA f) :
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
  Inductive ptree_R (A1 A2 : Type) (A_R : A1 -> A2 -> Type) :
      ptree A1 -> ptree A2 -> Type :=
  | pnode_R (x1 : A1) (x2 : A2) (xR : A_R x1 x2)
      (f1 : pforest A1) (f2 : pforest A2)
      (fR : pforest_R A1 A2 A_R f1 f2) :
      ptree_R A1 A2 A_R (@pnode A1 x1 f1) (@pnode A2 x2 f2)
  with pforest_R (A1 A2 : Type) (A_R : A1 -> A2 -> Type) :
      pforest A1 -> pforest A2 -> Type :=
  | pempty_R : pforest_R A1 A2 A_R (@pempty A1) (@pempty A2)
  | pcons_R (t1 : ptree A1) (t2 : ptree A2)
      (tR : ptree_R A1 A2 A_R t1 t2)
      (f1 : pforest A1) (f2 : pforest A2)
      (fR : pforest_R A1 A2 A_R f1 f2) :
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
    forall A (PA : A -> Type) (P : ptree A -> Type) (Q : pforest A -> Type),
      (forall x, PA x -> forall f (Pf : is_pforest A PA f),
        Q f -> P (@pnode A x f)) ->
      Q (@pempty A) ->
      (forall t (Pt : is_ptree A PA t), P t ->
       forall f (Pf : is_pforest A PA f), Q f -> Q (@pcons A t f)) ->
      forall t, is_ptree A PA t -> P t.
End ParametrizedMutualInductionExpected.

Module Type ParametrizedMutualTagExpected.
  Include ParametrizedMutualBase.
  Parameter ptree_tag : forall A : Type, ptree A -> BinNums.positive.
End ParametrizedMutualTagExpected.

Module Type ParametrizedMutualFieldsExpected.
  Include ParametrizedMutualTagExpected.
  Record box_ptree_pnode (A : Type) : Type := Box_ptree_pnode {
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
End ParametrizedMutualEqbOKExpected.

Module MutualMap <: MutualMapExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(map)] derive tree.
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
End MutualParam1.

Module MutualParam1Congr <: MutualParam1CongrExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1_congr)] derive tree.
End MutualParam1Congr.

Module MutualParam1Trivial <: MutualParam1TrivialExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1_trivial)] derive tree.
End MutualParam1Trivial.

Module MutualParam1Functor <: MutualParam1FunctorExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param1_functor)] derive tree.
End MutualParam1Functor.

Module MutualParam2 <: MutualParam2Expected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(param2)] derive tree.
End MutualParam2.

Module MutualInduction <: MutualInductionExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(induction)] derive tree.
End MutualInduction.

Module MutualTag <: MutualTagExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(tag)] derive tree.
End MutualTag.

Module MutualFields <: MutualFieldsExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(fields)] derive tree.
End MutualFields.

Module MutualEqb <: MutualEqbExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(eqb)] derive tree.
End MutualEqb.

Module MutualEqbCorrect <: MutualEqbCorrectExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(eqbcorrect)] derive tree.
End MutualEqbCorrect.

Module MutualEqbOK <: MutualEqbOKExpected.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(eqbOK)] derive tree.
End MutualEqbOK.

Module ParametrizedMutualMap <: ParametrizedMutualMapExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(map)] derive ptree.
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
End ParametrizedMutualParam1.

Module ParametrizedMutualParam1Congr <: ParametrizedMutualParam1CongrExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param1_congr)] derive ptree.
End ParametrizedMutualParam1Congr.

Module ParametrizedMutualParam1Trivial <: ParametrizedMutualParam1TrivialExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param1_trivial)] derive ptree.
End ParametrizedMutualParam1Trivial.

Module ParametrizedMutualParam1Functor <: ParametrizedMutualParam1FunctorExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param1_functor)] derive ptree.
End ParametrizedMutualParam1Functor.

Module ParametrizedMutualParam2 <: ParametrizedMutualParam2Expected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(param2)] derive ptree.
End ParametrizedMutualParam2.

Module ParametrizedMutualInduction <: ParametrizedMutualInductionExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(induction)] derive ptree.
End ParametrizedMutualInduction.

Module ParametrizedMutualTag <: ParametrizedMutualTagExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(tag)] derive ptree.
End ParametrizedMutualTag.

Module ParametrizedMutualFields <: ParametrizedMutualFieldsExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(fields)] derive ptree.
End ParametrizedMutualFields.

Module ParametrizedMutualEqb <: ParametrizedMutualEqbExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(eqb)] derive ptree.
End ParametrizedMutualEqb.

Module ParametrizedMutualEqbCorrect <: ParametrizedMutualEqbCorrectExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(eqbcorrect)] derive ptree.
End ParametrizedMutualEqbCorrect.

Module ParametrizedMutualEqbOK <: ParametrizedMutualEqbOKExpected.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(eqbOK)] derive ptree.
End ParametrizedMutualEqbOK.
