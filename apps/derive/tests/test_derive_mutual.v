(* This is the same derivation set exported by derive.std, kept explicit so
   each standard derivation is tested independently.  Each derive call below
   lives in its own module and is checked against a signature documenting the
   Coq definitions that derivation is expected to add. *)
From Corelib Require Import BinNums Nat ssrbool.
Definition bool_is_true := is_true.
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
  Definition tree_map : tree -> tree :=
  fun x : tree => x.
  Definition forest_map : forest -> forest :=
  fun x : forest => x.
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
  Definition reali_is_tree : param1.reali_db tree is_tree :=
  @param1.store_reali _ _ tree is_tree.
  Definition reali_is_forest : param1.reali_db forest is_forest :=
  @param1.store_reali _ _ forest is_forest.
  Definition reali_is_tree_node : param1.reali_db node is_node :=
  @param1.store_reali _ _ node is_node.
  Definition reali_is_forest_empty : param1.reali_db empty is_empty :=
  @param1.store_reali _ _ empty is_empty.
  Definition reali_is_forest_cons : param1.reali_db cons is_cons :=
  @param1.store_reali _ _ cons is_cons.
End MutualParam1Expected.

Module Type MutualParam1CongrExpected.
  Include MutualParam1Expected.
  Definition congr_is_node : forall (x : forest)
         (p1 p2 : is_forest x),
       p1 = p2 ->
       is_node x p1 = is_node x p2 :=
  fun (x : forest) (p1 p2 : is_forest x)
    (e : p1 = p2) =>
  match
    e in _ = i
    return is_node x p1 = is_node x i
  with
  | eq_refl => eq_refl
  end.
  Definition congr_is_empty : is_empty = is_empty :=
  eq_refl.
  Definition congr_is_cons : forall (x : tree)
         (p1 p2 : is_tree x),
       p1 = p2 ->
       forall (x0 : forest)
         (p3 p4 : is_forest x0),
       p3 = p4 ->
       is_cons x p1 x0 p3 =
       is_cons x p2 x0 p4 :=
  fun (x : tree) (p1 p2 : is_tree x)
    (e : p1 = p2) =>
  match
    e in _ = i
    return
      (forall (x0 : forest)
         (p3 p4 : is_forest x0),
       p3 = p4 ->
       is_cons x p1 x0 p3 =
       is_cons x i x0 p4)
  with
  | eq_refl =>
      fun (x0 : forest)
        (p3 p4 : is_forest x0) (e0 : p3 = p4) =>
      match
        e0 in _ = i
        return
          is_cons x p1 x0 p3 =
          is_cons x p1 x0 i
      with
      | eq_refl => eq_refl
      end
  end.
End MutualParam1CongrExpected.

Module Type MutualParam1TrivialExpected.
  Include MutualParam1CongrExpected.
  Definition is_tree_inhab : forall x : tree, is_tree x :=
  fix is_tree_inhab_rec (x : tree) :
      is_tree x :=
    match x as i return is_tree i with
    | node f =>
        is_node f (is_forest_inhab_rec f)
    end
  with is_forest_inhab_rec (x : forest) :
      is_forest x :=
    match x as i return is_forest i with
    | empty => is_empty
    | cons t f =>
        is_cons t (is_tree_inhab_rec t) f
          (is_forest_inhab_rec f)
    end
  for
  is_tree_inhab_rec.
  Definition is_forest_inhab : forall x : forest, is_forest x :=
  fix is_tree_inhab_rec (x : tree) :
      is_tree x :=
    match x as i return is_tree i with
    | node f =>
        is_node f (is_forest_inhab_rec f)
    end
  with is_forest_inhab_rec (x : forest) :
      is_forest x :=
    match x as i return is_forest i with
    | empty => is_empty
    | cons t f =>
        is_cons t (is_tree_inhab_rec t) f
          (is_forest_inhab_rec f)
    end
  for
  is_forest_inhab_rec.
  Definition is_tree_trivial : forall x : tree,
       {u : is_tree x &
       forall v : is_tree x, u = v} :=
  fun x : tree =>
  param1.contracts tree is_tree x
    (is_tree_inhab x)
    ((fix is_tree_trivial_rec
        (x0 : tree) (y : is_tree x0)
        {struct y} : is_tree_inhab x0 = y :=
        match
          y as i in is_tree s1
          return is_tree_inhab s1 = i
        with
        | is_node f Pf =>
            match
              param1.trivial_uniq forest
                is_forest
                (fun x1 : forest =>
                 param1.contracts forest
                   is_forest x1
                   (is_forest_inhab x1)
                   (is_forest_trivial_rec x1))
                f Pf
              in _ = H
              return
                is_node f
                  (param1.trivial_full forest
                     is_forest
                     (fun x1 : forest =>
                      param1.contracts forest
                        is_forest x1
                        (is_forest_inhab x1)
                        (is_forest_trivial_rec x1))
                     f) =
                is_node f H
            with
            | eq_refl => eq_refl
            end
        end
      with is_forest_trivial_rec
        (x0 : forest)
        (y : is_forest x0) {struct y} :
          is_forest_inhab x0 = y :=
        match
          y as i in is_forest s1
          return is_forest_inhab s1 = i
        with
        | is_empty => eq_refl
        | is_cons t Pt f Pf =>
            match
              param1.trivial_uniq forest
                is_forest
                (fun x1 : forest =>
                 param1.contracts forest
                   is_forest x1
                   (is_forest_inhab x1)
                   (is_forest_trivial_rec x1))
                f Pf
              in _ = H
              return
                is_cons t
                  (param1.trivial_full tree
                     is_tree
                     (fun x1 : tree =>
                      param1.contracts tree
                        is_tree x1
                        (is_tree_inhab x1)
                        (is_tree_trivial_rec x1))
                     t)
                  f
                  (param1.trivial_full forest
                     is_forest
                     (fun x1 : forest =>
                      param1.contracts forest
                        is_forest x1
                        (is_forest_inhab x1)
                        (is_forest_trivial_rec x1))
                     f) =
                is_cons t Pt f H
            with
            | eq_refl =>
                match
                  param1.trivial_uniq tree
                    is_tree
                    (fun x1 : tree =>
                     param1.contracts tree
                       is_tree x1
                       (is_tree_inhab x1)
                       (is_tree_trivial_rec x1))
                    t Pt
                  in _ = H
                  return
                    is_cons t
                      (param1.trivial_full tree
                         is_tree
                         (fun x1 : tree =>
                          param1.contracts tree
                            is_tree x1
                            (is_tree_inhab x1)
                            (is_tree_trivial_rec x1))
                         t)
                      f
                      (param1.trivial_full forest
                         is_forest
                         (fun x1 : forest =>
                          param1.contracts forest
                            is_forest x1
                            (is_forest_inhab x1)
                            (is_forest_trivial_rec x1))
                         f) =
                    is_cons t H f
                      (param1.trivial_full forest
                         is_forest
                         (fun x1 : forest =>
                          param1.contracts forest
                            is_forest x1
                            (is_forest_inhab x1)
                            (is_forest_trivial_rec x1))
                         f)
                with
                | eq_refl => eq_refl
                end
            end
        end
      for
      is_tree_trivial_rec) x).
  Definition is_forest_trivial : forall x : forest,
       {u : is_forest x &
       forall v : is_forest x, u = v} :=
  fun x : forest =>
  param1.contracts forest is_forest x
    (is_forest_inhab x)
    ((fix is_tree_trivial_rec
        (x0 : tree) (y : is_tree x0)
        {struct y} : is_tree_inhab x0 = y :=
        match
          y as i in is_tree s1
          return is_tree_inhab s1 = i
        with
        | is_node f Pf =>
            match
              param1.trivial_uniq forest
                is_forest
                (fun x1 : forest =>
                 param1.contracts forest
                   is_forest x1
                   (is_forest_inhab x1)
                   (is_forest_trivial_rec x1))
                f Pf
              in _ = H
              return
                is_node f
                  (param1.trivial_full forest
                     is_forest
                     (fun x1 : forest =>
                      param1.contracts forest
                        is_forest x1
                        (is_forest_inhab x1)
                        (is_forest_trivial_rec x1))
                     f) =
                is_node f H
            with
            | eq_refl => eq_refl
            end
        end
      with is_forest_trivial_rec
        (x0 : forest)
        (y : is_forest x0) {struct y} :
          is_forest_inhab x0 = y :=
        match
          y as i in is_forest s1
          return is_forest_inhab s1 = i
        with
        | is_empty => eq_refl
        | is_cons t Pt f Pf =>
            match
              param1.trivial_uniq forest
                is_forest
                (fun x1 : forest =>
                 param1.contracts forest
                   is_forest x1
                   (is_forest_inhab x1)
                   (is_forest_trivial_rec x1))
                f Pf
              in _ = H
              return
                is_cons t
                  (param1.trivial_full tree
                     is_tree
                     (fun x1 : tree =>
                      param1.contracts tree
                        is_tree x1
                        (is_tree_inhab x1)
                        (is_tree_trivial_rec x1))
                     t)
                  f
                  (param1.trivial_full forest
                     is_forest
                     (fun x1 : forest =>
                      param1.contracts forest
                        is_forest x1
                        (is_forest_inhab x1)
                        (is_forest_trivial_rec x1))
                     f) =
                is_cons t Pt f H
            with
            | eq_refl =>
                match
                  param1.trivial_uniq tree
                    is_tree
                    (fun x1 : tree =>
                     param1.contracts tree
                       is_tree x1
                       (is_tree_inhab x1)
                       (is_tree_trivial_rec x1))
                    t Pt
                  in _ = H
                  return
                    is_cons t
                      (param1.trivial_full tree
                         is_tree
                         (fun x1 : tree =>
                          param1.contracts tree
                            is_tree x1
                            (is_tree_inhab x1)
                            (is_tree_trivial_rec x1))
                         t)
                      f
                      (param1.trivial_full forest
                         is_forest
                         (fun x1 : forest =>
                          param1.contracts forest
                            is_forest x1
                            (is_forest_inhab x1)
                            (is_forest_trivial_rec x1))
                         f) =
                    is_cons t H f
                      (param1.trivial_full forest
                         is_forest
                         (fun x1 : forest =>
                          param1.contracts forest
                            is_forest x1
                            (is_forest_inhab x1)
                            (is_forest_trivial_rec x1))
                         f)
                with
                | eq_refl => eq_refl
                end
            end
        end
      for
      is_forest_trivial_rec) x).
End MutualParam1TrivialExpected.

Module Type MutualParam1FunctorExpected.
  Include MutualParam1Expected.
  Definition is_tree_functor : forall x : tree,
       is_tree x -> is_tree x :=
  fix is_tree_functor_rec
    (x : tree) (x0 : is_tree x) {struct
     x0} : is_tree x :=
    match
      x0 in is_tree s1
      return is_tree s1
    with
    | is_node f Pf => is_node f Pf
    end
  with is_forest_functor_rec
    (x : forest) (x0 : is_forest x)
    {struct x0} : is_forest x :=
    match
      x0 in is_forest s1
      return is_forest s1
    with
    | is_empty => is_empty
    | is_cons t Pt f Pf =>
        is_cons t Pt f Pf
    end
  for
  is_tree_functor_rec.
  Definition is_forest_functor : forall x : forest,
       is_forest x -> is_forest x :=
  fix is_tree_functor_rec
    (x : tree) (x0 : is_tree x) {struct
     x0} : is_tree x :=
    match
      x0 in is_tree s1
      return is_tree s1
    with
    | is_node f Pf => is_node f Pf
    end
  with is_forest_functor_rec
    (x : forest) (x0 : is_forest x)
    {struct x0} : is_forest x :=
    match
      x0 in is_forest s1
      return is_forest s1
    with
    | is_empty => is_empty
    | is_cons t Pt f Pf =>
        is_cons t Pt f Pf
    end
  for
  is_forest_functor_rec.
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
  Definition param_tree_R : param2.param_db tree tree
         tree_R :=
  @param2.store_param _ _ _ tree tree tree_R.
  Definition param_forest_R : param2.param_db forest forest
         forest_R :=
  @param2.store_param _ _ _ forest forest forest_R.
  Definition param_node_R : param2.param_db node node
         node_R :=
  @param2.store_param _ _ _ node node node_R.
  Definition param_empty_R : param2.param_db empty empty
         empty_R :=
  @param2.store_param _ _ _ empty empty empty_R.
  Definition param_cons_R : param2.param_db cons cons
         cons_R :=
  @param2.store_param _ _ _ cons cons cons_R.
End MutualParam2Expected.

Module Type MutualInductionExpected.
  Include MutualParam1FunctorExpected.
  Definition tree_induction : forall (P : tree -> Type)
         (P0 : forest -> Type),
       (forall f : forest,
        is_forest f -> P0 f -> P (node f)) ->
       P0 empty ->
       (forall t : tree,
        is_tree t ->
        P t ->
        forall f : forest,
        is_forest f -> P0 f -> P0 (cons t f)) ->
       forall s1 : tree, is_tree s1 -> P s1 :=
  fun (P : tree -> Type) (P0 : forest -> Type)
    (His_node : forall f : forest,
                is_forest f ->
                P0 f -> P (node f))
    (His_empty : P0 empty)
    (His_cons : forall t : tree,
                is_tree t ->
                P t ->
                forall f : forest,
                is_forest f ->
                P0 f -> P0 (cons t f)) =>
  fix is_tree_induction_rec
    (s1 : tree) (H : is_tree s1) {struct H} :
      P s1 :=
    match H in is_tree s2 return P s2 with
    | is_node f Pf =>
        His_node f Pf (is_forest_induction_rec f Pf)
    end
  with is_forest_induction_rec
    (s1 : forest) (H : is_forest s1) {struct H} :
      P0 s1 :=
    match H in is_forest s2 return P0 s2 with
    | is_empty => His_empty
    | is_cons t Pt f Pf =>
        His_cons t Pt (is_tree_induction_rec t Pt) f Pf
          (is_forest_induction_rec f Pf)
    end
  for
  is_tree_induction_rec.
End MutualInductionExpected.

Module Type MutualTagExpected.
  Include MutualBase.
  Definition tree_tag : tree -> BinNums.positive :=
  fun i : tree => match i with
                            | node _ => BinNums.xH
                            end.
  Definition forest_tag : forest -> BinNums.positive :=
  fun i : forest =>
  match i with
  | empty => BinNums.xH
  | cons _ _ => BinNums.xO BinNums.xH
  end.
End MutualTagExpected.

Module Type MutualFieldsExpected.
  Include MutualTagExpected.
  Universe box_tree_node_u box_forest_empty_u box_forest_cons_u.
  Constraint Set < box_tree_node_u.
  Constraint Set < box_forest_empty_u.
  Constraint Set < box_forest_cons_u.
  Record box_tree_node : Type@{box_tree_node_u} := Box_tree_node { Box_tree_node_0 : forest }.
  Record box_forest_empty : Type@{box_forest_empty_u} := Box_forest_empty {}.
  Record box_forest_cons : Type@{box_forest_cons_u} := Box_forest_cons {
    Box_forest_cons_0 : tree;
    Box_forest_cons_1 : forest;
  }.
  Definition tree_fields_t : BinNums.positive -> Type :=
  fun _ : BinNums.positive => box_tree_node.
  Definition tree_fields : forall i : tree,
       tree_fields_t (tree_tag i) :=
  fun i : tree =>
  match
    i as i0 return tree_fields_t (tree_tag i0)
  with
  | node f => {| Box_tree_node_0 := f |}
  end.
  Definition tree_construct : BinNums.positive ->
       box_tree_node -> option tree :=
  fun (_ : BinNums.positive) (b : box_tree_node) =>
  match b with
  | {| Box_tree_node_0 := Box_tree_node_0 |} =>
      Some (node Box_tree_node_0)
  end.
  Definition tree_constructP : forall i : tree,
       tree_construct (tree_tag i)
         (tree_fields i) =
       Some i :=
  fun i : tree =>
  match
    i as i0
    return
      tree_construct (tree_tag i0)
        (tree_fields i0) =
      Some i0
  with
  | node f => eq_refl
  end.
  Definition forest_fields_t : BinNums.positive -> Type :=
  fun p : BinNums.positive =>
  match p with
  | BinNums.xI _ => unit
  | BinNums.xO _ => box_forest_cons
  | BinNums.xH => box_forest_empty
  end.
  Definition forest_fields : forall i : forest,
       forest_fields_t (forest_tag i) :=
  fun i : forest =>
  match
    i as i0 return forest_fields_t (forest_tag i0)
  with
  | empty => Box_forest_empty
  | cons t f =>
      {|
        Box_forest_cons_0 := t;
        Box_forest_cons_1 := f
      |}
  end.
  Definition forest_construct : forall p : BinNums.positive,
       forest_fields_t p -> option forest :=
  fun p : BinNums.positive =>
  match
    p as i return forest_fields_t i -> option forest
  with
  | BinNums.xI _ => fun _ : unit => None
  | BinNums.xO _ =>
      fun b : box_forest_cons =>
      match b with
      | {|
          Box_forest_cons_0 := Box_forest_cons_0;
          Box_forest_cons_1 := Box_forest_cons_1
        |} => Some (cons Box_forest_cons_0 Box_forest_cons_1)
      end
  | BinNums.xH =>
      fun _ : box_forest_empty => Some empty
  end.
  Definition forest_constructP : forall i : forest,
       forest_construct (forest_tag i)
         (forest_fields i) =
       Some i :=
  fun i : forest =>
  match
    i as i0
    return
      forest_construct (forest_tag i0)
        (forest_fields i0) =
      Some i0
  with
  | empty => eq_refl
  | cons t f => eq_refl
  end.
End MutualFieldsExpected.

Module Type MutualEqbExpected.
  Include MutualFieldsExpected.
  Definition tree_eqb : tree -> tree -> bool :=
  fix tree (x1 x2 : tree) {struct x1} : bool :=
    match x1 with
    | node f =>
        eqb_core_defs.eqb_body (tagB:=tree_tag)
          (fields_tA:=fun _ : BinNums.positive => box_tree_node)
          (fields_tB:=tree_fields_t) tree_fields
          (fun (_ : BinNums.positive) (a b : box_tree_node) =>
           match a with
           | {| Box_tree_node_0 := Box_tree_node_0 |} =>
               match b with
               | {| Box_tree_node_0 := Box_tree_node_1 |} =>
                   (forest Box_tree_node_0 Box_tree_node_1 && true)%bool
               end
           end)
          (t1:=tree_tag (node f))
          {| Box_tree_node_0 := f |} x2
    end
  with forest (x1 x2 : forest) {struct x1} : bool :=
    match x1 with
    | empty =>
        eqb_core_defs.eqb_body (tagB:=forest_tag)
          (fields_tA:=forest_fields_t)
          (fields_tB:=forest_fields_t) forest_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               forest_fields_t i ->
               forest_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_forest_cons =>
               match a with
               | {|
                   Box_forest_cons_0 := Box_forest_cons_0;
                   Box_forest_cons_1 := Box_forest_cons_1
                 |} =>
                   match b with
                   | {|
                       Box_forest_cons_0 := Box_forest_cons_2;
                       Box_forest_cons_1 := Box_forest_cons_3
                     |} =>
                       (tree Box_forest_cons_0 Box_forest_cons_2 &&
                        (forest Box_forest_cons_1 Box_forest_cons_3 && true))%bool
                   end
               end
           | BinNums.xH => fun _ _ : box_forest_empty => true
           end)
          (t1:=forest_tag empty) Box_forest_empty
          x2
    | cons t f =>
        eqb_core_defs.eqb_body (tagB:=forest_tag)
          (fields_tA:=forest_fields_t)
          (fields_tB:=forest_fields_t) forest_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               forest_fields_t i ->
               forest_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_forest_cons =>
               match a with
               | {|
                   Box_forest_cons_0 := Box_forest_cons_0;
                   Box_forest_cons_1 := Box_forest_cons_1
                 |} =>
                   match b with
                   | {|
                       Box_forest_cons_0 := Box_forest_cons_2;
                       Box_forest_cons_1 := Box_forest_cons_3
                     |} =>
                       (tree Box_forest_cons_0 Box_forest_cons_2 &&
                        (forest Box_forest_cons_1 Box_forest_cons_3 && true))%bool
                   end
               end
           | BinNums.xH => fun _ _ : box_forest_empty => true
           end)
          (t1:=forest_tag (cons t f))
          {|
            Box_forest_cons_0 := t; Box_forest_cons_1 := f
          |} x2
    end
  for
  tree.
  Definition forest_eqb : forest -> forest -> bool :=
  fix tree (x1 x2 : tree) {struct x1} : bool :=
    match x1 with
    | node f =>
        eqb_core_defs.eqb_body (tagB:=tree_tag)
          (fields_tA:=fun _ : BinNums.positive => box_tree_node)
          (fields_tB:=tree_fields_t) tree_fields
          (fun (_ : BinNums.positive) (a b : box_tree_node) =>
           match a with
           | {| Box_tree_node_0 := Box_tree_node_0 |} =>
               match b with
               | {| Box_tree_node_0 := Box_tree_node_1 |} =>
                   (forest Box_tree_node_0 Box_tree_node_1 && true)%bool
               end
           end)
          (t1:=tree_tag (node f))
          {| Box_tree_node_0 := f |} x2
    end
  with forest (x1 x2 : forest) {struct x1} : bool :=
    match x1 with
    | empty =>
        eqb_core_defs.eqb_body (tagB:=forest_tag)
          (fields_tA:=forest_fields_t)
          (fields_tB:=forest_fields_t) forest_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               forest_fields_t i ->
               forest_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_forest_cons =>
               match a with
               | {|
                   Box_forest_cons_0 := Box_forest_cons_0;
                   Box_forest_cons_1 := Box_forest_cons_1
                 |} =>
                   match b with
                   | {|
                       Box_forest_cons_0 := Box_forest_cons_2;
                       Box_forest_cons_1 := Box_forest_cons_3
                     |} =>
                       (tree Box_forest_cons_0 Box_forest_cons_2 &&
                        (forest Box_forest_cons_1 Box_forest_cons_3 && true))%bool
                   end
               end
           | BinNums.xH => fun _ _ : box_forest_empty => true
           end)
          (t1:=forest_tag empty) Box_forest_empty
          x2
    | cons t f =>
        eqb_core_defs.eqb_body (tagB:=forest_tag)
          (fields_tA:=forest_fields_t)
          (fields_tB:=forest_fields_t) forest_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               forest_fields_t i ->
               forest_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_forest_cons =>
               match a with
               | {|
                   Box_forest_cons_0 := Box_forest_cons_0;
                   Box_forest_cons_1 := Box_forest_cons_1
                 |} =>
                   match b with
                   | {|
                       Box_forest_cons_0 := Box_forest_cons_2;
                       Box_forest_cons_1 := Box_forest_cons_3
                     |} =>
                       (tree Box_forest_cons_0 Box_forest_cons_2 &&
                        (forest Box_forest_cons_1 Box_forest_cons_3 && true))%bool
                   end
               end
           | BinNums.xH => fun _ _ : box_forest_empty => true
           end)
          (t1:=forest_tag (cons t f))
          {|
            Box_forest_cons_0 := t; Box_forest_cons_1 := f
          |} x2
    end
  for
  forest.
  Definition tree_eqb_fields : (tree -> tree -> bool) ->
       BinNums.positive ->
       box_tree_node -> box_tree_node -> bool :=
  fun (_ : tree -> tree -> bool) 
    (_ : BinNums.positive) (a b : box_tree_node) =>
  match a with
  | {| Box_tree_node_0 := Box_tree_node_0 |} =>
      match b with
      | {| Box_tree_node_0 := Box_tree_node_1 |} =>
          (forest_eqb Box_tree_node_0 Box_tree_node_1 && true)%bool
      end
  end.
  Definition forest_eqb_fields : (forest -> forest -> bool) ->
       forall x : BinNums.positive,
       forest_fields_t x -> forest_fields_t x -> bool :=
  fun (rec : forest -> forest -> bool)
    (x : BinNums.positive) =>
  match
    x as i
    return forest_fields_t i -> forest_fields_t i -> bool
  with
  | BinNums.xI _ => fun _ _ : unit => true
  | BinNums.xO _ =>
      fun a b : box_forest_cons =>
      match a with
      | {|
          Box_forest_cons_0 := Box_forest_cons_0;
          Box_forest_cons_1 := Box_forest_cons_1
        |} =>
          match b with
          | {|
              Box_forest_cons_0 := Box_forest_cons_2;
              Box_forest_cons_1 := Box_forest_cons_3
            |} =>
              (tree_eqb Box_forest_cons_0 Box_forest_cons_2 &&
               (rec Box_forest_cons_1 Box_forest_cons_3 && true))%bool
          end
      end
  | BinNums.xH => fun _ _ : box_forest_empty => true
  end.
End MutualEqbExpected.

Module Type MutualEqbCorrectExpected.
  Include MutualEqbExpected.
  Universe tree_reali_u forest_reali_u.
  Constraint Set < tree_reali_u.
  Constraint Set < forest_reali_u.
  Inductive is_tree : tree -> Type@{tree_reali_u} :=
  | is_node (f : forest) (Pf : is_forest f) : is_tree (node f)
  with is_forest : forest -> Type@{forest_reali_u} :=
  | is_empty : is_forest empty
  | is_cons (t : tree) (Pt : is_tree t)
      (f : forest) (Pf : is_forest f) : is_forest (cons t f).
  Definition is_tree_inhab : forall x : tree, is_tree x :=
  fix is_tree_inhab_rec (x : tree) :
      is_tree x :=
    match x as i return is_tree i with
    | node f =>
        is_node f (is_forest_inhab_rec f)
    end
  with is_forest_inhab_rec (x : forest) :
      is_forest x :=
    match x as i return is_forest i with
    | empty => is_empty
    | cons t f =>
        is_cons t (is_tree_inhab_rec t) f
          (is_forest_inhab_rec f)
    end
  for
  is_tree_inhab_rec.
  Definition is_forest_inhab : forall x : forest, is_forest x :=
  fix is_tree_inhab_rec (x : tree) :
      is_tree x :=
    match x as i return is_tree i with
    | node f =>
        is_node f (is_forest_inhab_rec f)
    end
  with is_forest_inhab_rec (x : forest) :
      is_forest x :=
    match x as i return is_forest i with
    | empty => is_empty
    | cons t f =>
        is_cons t (is_tree_inhab_rec t) f
          (is_forest_inhab_rec f)
    end
  for
  is_forest_inhab_rec.
  Definition tree_induction : forall (P : tree -> Type)
         (P0 : forest -> Type),
       (forall f : forest,
        is_forest f -> P0 f -> P (node f)) ->
       P0 empty ->
       (forall t : tree,
        is_tree t ->
        P t ->
        forall f : forest,
        is_forest f ->
        P0 f -> P0 (cons t f)) ->
       forall s1 : tree, is_tree s1 -> P s1 :=
  fun (P : tree -> Type)
    (P0 : forest -> Type)
    (His_node : forall f : forest,
                is_forest f ->
                P0 f -> P (node f))
    (His_empty : P0 empty)
    (His_cons : forall t : tree,
                is_tree t ->
                P t ->
                forall f : forest,
                is_forest f ->
                P0 f -> P0 (cons t f)) =>
  fix is_tree_induction_rec
    (s1 : tree) (H : is_tree s1) {struct H} :
      P s1 :=
    match H in is_tree s2 return P s2 with
    | is_node f Pf =>
        His_node f Pf (is_forest_induction_rec f Pf)
    end
  with is_forest_induction_rec
    (s1 : forest) (H : is_forest s1) {struct
     H} : P0 s1 :=
    match H in is_forest s2 return P0 s2 with
    | is_empty => His_empty
    | is_cons t Pt f Pf =>
        His_cons t Pt (is_tree_induction_rec t Pt) f Pf
          (is_forest_induction_rec f Pf)
    end
  for
  is_tree_induction_rec.
  Definition forest_induction : forall (P : tree -> Type)
         (P0 : forest -> Type),
       (forall f : forest,
        is_forest f -> P0 f -> P (node f)) ->
       P0 empty ->
       (forall t : tree,
        is_tree t ->
        P t ->
        forall f : forest,
        is_forest f ->
        P0 f -> P0 (cons t f)) ->
       forall s1 : forest,
       is_forest s1 -> P0 s1 :=
  fun (P : tree -> Type)
    (P0 : forest -> Type)
    (His_node : forall f : forest,
                is_forest f ->
                P0 f -> P (node f))
    (His_empty : P0 empty)
    (His_cons : forall t : tree,
                is_tree t ->
                P t ->
                forall f : forest,
                is_forest f ->
                P0 f -> P0 (cons t f)) =>
  fix is_tree_induction_rec
    (s1 : tree) (H : is_tree s1) {struct H} :
      P s1 :=
    match H in is_tree s2 return P s2 with
    | is_node f Pf =>
        His_node f Pf (is_forest_induction_rec f Pf)
    end
  with is_forest_induction_rec
    (s1 : forest) (H : is_forest s1) {struct
     H} : P0 s1 :=
    match H in is_forest s2 return P0 s2 with
    | is_empty => His_empty
    | is_cons t Pt f Pf =>
        His_cons t Pt (is_tree_induction_rec t Pt) f Pf
          (is_forest_induction_rec f Pf)
    end
  for
  is_forest_induction_rec.
  Definition tree_eqb_correct : forall x : tree, @eqb_correct_on tree tree_eqb x :=
  fun x : tree =>
  let common :
    forall (a1 : tree)
      (_ : @eqb_fields_correct_on tree tree_tag tree_fields_t tree_fields
             tree_construct (tree_eqb_fields tree_eqb) a1)
      (a2 : tree)
      (_ : Datatypes.is_true
             (@eqb_body tree tree_tag tree_fields_t tree_fields_t tree_fields
                (tree_eqb_fields tree_eqb) (tree_tag a1) 
                (tree_fields a1) a2)),
    @eq tree a1 a2 :=
    @eqb_body_correct tree tree_tag tree_fields_t tree_fields tree_construct
      tree_constructP (tree_eqb_fields tree_eqb)
    in
  let common0 :
    forall (a1 : forest)
      (_ : @eqb_fields_correct_on forest forest_tag forest_fields_t
             forest_fields forest_construct (forest_eqb_fields forest_eqb) a1)
      (a2 : forest)
      (_ : Datatypes.is_true
             (@eqb_body forest forest_tag forest_fields_t forest_fields_t
                forest_fields (forest_eqb_fields forest_eqb) 
                (forest_tag a1) (forest_fields a1) a2)),
    @eq forest a1 a2 :=
    @eqb_body_correct forest forest_tag forest_fields_t forest_fields
      forest_construct forest_constructP (forest_eqb_fields forest_eqb)
    in
  tree_induction (@eqb_correct_on tree tree_eqb)
    (@eqb_correct_on forest forest_eqb)
    (fun (x0 : forest) (_ : is_forest x0)
       (h : @eqb_correct_on forest forest_eqb x0) =>
     common (node x0)
       (fun x1 : tree_fields_t (tree_tag (node x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (tree_eqb_fields tree_eqb (tree_tag (node x0))
                        (tree_fields (node x0)) i)
                     true,
             @eq (option tree) (@Some tree (node x0))
               (tree_construct (tree_tag (node x0)) i))
        with
        | Box_tree_node Box_tree_node_0 =>
            @impliesP (bcons (forest_eqb x0 Box_tree_node_0) bnil)
              (@eq (option tree) (@Some tree (node x0))
                 (tree_construct (tree_tag (node x0))
                    (Box_tree_node Box_tree_node_0)))
              (fun h0 : @eq bool (forest_eqb x0 Box_tree_node_0) true =>
               @eq_ind_r_nP (tcons forest tnil)
                 (fun w : forest =>
                  @eq (option tree) (@Some tree (node x0))
                    (tree_construct (tree_tag (node x0)) (Box_tree_node w)))
                 x0 Box_tree_node_0 (h Box_tree_node_0 h0)
                 (@eq_refl (option tree) (@Some tree (node x0))))
        end)
     :
     @eqb_correct_on tree tree_eqb (node x0))
    (common0 empty
       (fun x0 : forest_fields_t (forest_tag empty) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (forest_eqb_fields forest_eqb (forest_tag empty)
                        (forest_fields empty) i)
                     true,
             @eq (option forest) (@Some forest empty)
               (forest_construct (forest_tag empty) i))
        with
        | Box_forest_empty =>
            @impliesP bnil
              (@eq (option forest) (@Some forest empty)
                 (forest_construct (forest_tag empty) Box_forest_empty))
              (@eq_ind_r_nP tnil
                 (@eq (option forest) (@Some forest empty)
                    (forest_construct (forest_tag empty) Box_forest_empty))
                 (@eq_refl (option forest) (@Some forest empty)))
        end)
     :
     @eqb_correct_on forest forest_eqb empty)
    (fun (x0 : tree) (_ : is_tree x0) (h : @eqb_correct_on tree tree_eqb x0)
       (x1 : forest) (_ : is_forest x1)
       (h0 : @eqb_correct_on forest forest_eqb x1) =>
     common0 (cons x0 x1)
       (fun x2 : forest_fields_t (forest_tag (cons x0 x1)) =>
        match
          x2 as i
          return
            (forall
               _ : @eq bool
                     (forest_eqb_fields forest_eqb (forest_tag (cons x0 x1))
                        (forest_fields (cons x0 x1)) i)
                     true,
             @eq (option forest) (@Some forest (cons x0 x1))
               (forest_construct (forest_tag (cons x0 x1)) i))
        with
        | Box_forest_cons Box_forest_cons_0 Box_forest_cons_1 =>
            @impliesP
              (bcons (tree_eqb x0 Box_forest_cons_0)
                 (bcons (forest_eqb x1 Box_forest_cons_1) bnil))
              (@eq (option forest) (@Some forest (cons x0 x1))
                 (forest_construct (forest_tag (cons x0 x1))
                    (Box_forest_cons Box_forest_cons_0 Box_forest_cons_1)))
              (fun (h1 : @eq bool (tree_eqb x0 Box_forest_cons_0) true)
                 (h2 : @eq bool (forest_eqb x1 Box_forest_cons_1) true) =>
               @eq_ind_r_nP (tcons tree (tcons forest tnil))
                 (fun (w : tree) (w0 : forest) =>
                  @eq (option forest) (@Some forest (cons x0 x1))
                    (forest_construct (forest_tag (cons x0 x1))
                       (Box_forest_cons w w0)))
                 x0 Box_forest_cons_0 (h Box_forest_cons_0 h1) x1
                 Box_forest_cons_1 (h0 Box_forest_cons_1 h2)
                 (@eq_refl (option forest) (@Some forest (cons x0 x1))))
        end)
     :
     @eqb_correct_on forest forest_eqb (cons x0 x1))
    x (is_tree_inhab x).
  Definition forest_eqb_correct : forall x : forest, @eqb_correct_on forest forest_eqb x :=
  fun x : forest =>
  let common :
    forall (a1 : tree)
      (_ : @eqb_fields_correct_on tree tree_tag tree_fields_t tree_fields
             tree_construct (tree_eqb_fields tree_eqb) a1)
      (a2 : tree)
      (_ : Datatypes.is_true
             (@eqb_body tree tree_tag tree_fields_t tree_fields_t tree_fields
                (tree_eqb_fields tree_eqb) (tree_tag a1) 
                (tree_fields a1) a2)),
    @eq tree a1 a2 :=
    @eqb_body_correct tree tree_tag tree_fields_t tree_fields tree_construct
      tree_constructP (tree_eqb_fields tree_eqb)
    in
  let common0 :
    forall (a1 : forest)
      (_ : @eqb_fields_correct_on forest forest_tag forest_fields_t
             forest_fields forest_construct (forest_eqb_fields forest_eqb) a1)
      (a2 : forest)
      (_ : Datatypes.is_true
             (@eqb_body forest forest_tag forest_fields_t forest_fields_t
                forest_fields (forest_eqb_fields forest_eqb) 
                (forest_tag a1) (forest_fields a1) a2)),
    @eq forest a1 a2 :=
    @eqb_body_correct forest forest_tag forest_fields_t forest_fields
      forest_construct forest_constructP (forest_eqb_fields forest_eqb)
    in
  forest_induction (@eqb_correct_on tree tree_eqb)
    (@eqb_correct_on forest forest_eqb)
    (fun (x0 : forest) (_ : is_forest x0)
       (h : @eqb_correct_on forest forest_eqb x0) =>
     common (node x0)
       (fun x1 : tree_fields_t (tree_tag (node x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (tree_eqb_fields tree_eqb (tree_tag (node x0))
                        (tree_fields (node x0)) i)
                     true,
             @eq (option tree) (@Some tree (node x0))
               (tree_construct (tree_tag (node x0)) i))
        with
        | Box_tree_node Box_tree_node_0 =>
            @impliesP (bcons (forest_eqb x0 Box_tree_node_0) bnil)
              (@eq (option tree) (@Some tree (node x0))
                 (tree_construct (tree_tag (node x0))
                    (Box_tree_node Box_tree_node_0)))
              (fun h0 : @eq bool (forest_eqb x0 Box_tree_node_0) true =>
               @eq_ind_r_nP (tcons forest tnil)
                 (fun w : forest =>
                  @eq (option tree) (@Some tree (node x0))
                    (tree_construct (tree_tag (node x0)) (Box_tree_node w)))
                 x0 Box_tree_node_0 (h Box_tree_node_0 h0)
                 (@eq_refl (option tree) (@Some tree (node x0))))
        end)
     :
     @eqb_correct_on tree tree_eqb (node x0))
    (common0 empty
       (fun x0 : forest_fields_t (forest_tag empty) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (forest_eqb_fields forest_eqb (forest_tag empty)
                        (forest_fields empty) i)
                     true,
             @eq (option forest) (@Some forest empty)
               (forest_construct (forest_tag empty) i))
        with
        | Box_forest_empty =>
            @impliesP bnil
              (@eq (option forest) (@Some forest empty)
                 (forest_construct (forest_tag empty) Box_forest_empty))
              (@eq_ind_r_nP tnil
                 (@eq (option forest) (@Some forest empty)
                    (forest_construct (forest_tag empty) Box_forest_empty))
                 (@eq_refl (option forest) (@Some forest empty)))
        end)
     :
     @eqb_correct_on forest forest_eqb empty)
    (fun (x0 : tree) (_ : is_tree x0) (h : @eqb_correct_on tree tree_eqb x0)
       (x1 : forest) (_ : is_forest x1)
       (h0 : @eqb_correct_on forest forest_eqb x1) =>
     common0 (cons x0 x1)
       (fun x2 : forest_fields_t (forest_tag (cons x0 x1)) =>
        match
          x2 as i
          return
            (forall
               _ : @eq bool
                     (forest_eqb_fields forest_eqb (forest_tag (cons x0 x1))
                        (forest_fields (cons x0 x1)) i)
                     true,
             @eq (option forest) (@Some forest (cons x0 x1))
               (forest_construct (forest_tag (cons x0 x1)) i))
        with
        | Box_forest_cons Box_forest_cons_0 Box_forest_cons_1 =>
            @impliesP
              (bcons (tree_eqb x0 Box_forest_cons_0)
                 (bcons (forest_eqb x1 Box_forest_cons_1) bnil))
              (@eq (option forest) (@Some forest (cons x0 x1))
                 (forest_construct (forest_tag (cons x0 x1))
                    (Box_forest_cons Box_forest_cons_0 Box_forest_cons_1)))
              (fun (h1 : @eq bool (tree_eqb x0 Box_forest_cons_0) true)
                 (h2 : @eq bool (forest_eqb x1 Box_forest_cons_1) true) =>
               @eq_ind_r_nP (tcons tree (tcons forest tnil))
                 (fun (w : tree) (w0 : forest) =>
                  @eq (option forest) (@Some forest (cons x0 x1))
                    (forest_construct (forest_tag (cons x0 x1))
                       (Box_forest_cons w w0)))
                 x0 Box_forest_cons_0 (h Box_forest_cons_0 h1) x1
                 Box_forest_cons_1 (h0 Box_forest_cons_1 h2)
                 (@eq_refl (option forest) (@Some forest (cons x0 x1))))
        end)
     :
     @eqb_correct_on forest forest_eqb (cons x0 x1))
    x (is_forest_inhab x).
  Definition tree_eqb_refl : forall x : tree, @eqb_refl_on tree tree_eqb x :=
  fun x : tree =>
  let common :
    forall (a : tree)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on tree tree_tag tree_fields_t tree_fields
                (tree_eqb_fields tree_eqb) a)),
    Datatypes.is_true
      (@eqb_body tree tree_tag tree_fields_t tree_fields_t tree_fields
         (tree_eqb_fields tree_eqb) (tree_tag a) (tree_fields a) a) :=
    @eqb_body_refl tree tree_tag tree_fields_t tree_fields tree_construct
      tree_constructP (tree_eqb_fields tree_eqb)
    in
  let common0 :
    forall (a : forest)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on forest forest_tag forest_fields_t
                forest_fields (forest_eqb_fields forest_eqb) a)),
    Datatypes.is_true
      (@eqb_body forest forest_tag forest_fields_t forest_fields_t
         forest_fields (forest_eqb_fields forest_eqb) 
         (forest_tag a) (forest_fields a) a) :=
    @eqb_body_refl forest forest_tag forest_fields_t forest_fields
      forest_construct forest_constructP (forest_eqb_fields forest_eqb)
    in
  tree_induction (@eqb_refl_on tree tree_eqb) (@eqb_refl_on forest forest_eqb)
    (fun (x0 : forest) (_ : is_forest x0)
       (h : @eqb_refl_on forest forest_eqb x0) =>
     common (node x0) (eqb_refl_statementP (bcons (forest_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on tree tree_eqb (node x0))
    (common0 empty (eqb_refl_statementP bnil)
     :
     @eqb_refl_on forest forest_eqb empty)
    (fun (x0 : tree) (_ : is_tree x0) (h : @eqb_refl_on tree tree_eqb x0)
       (x1 : forest) (_ : is_forest x1)
       (h0 : @eqb_refl_on forest forest_eqb x1) =>
     common0 (cons x0 x1)
       (eqb_refl_statementP
          (bcons (forest_eqb x1 x1) (bcons (tree_eqb x0 x0) bnil)) h0 h)
     :
     @eqb_refl_on forest forest_eqb (cons x0 x1))
    x (is_tree_inhab x).
  Definition forest_eqb_refl : forall x : forest, @eqb_refl_on forest forest_eqb x :=
  fun x : forest =>
  let common :
    forall (a : tree)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on tree tree_tag tree_fields_t tree_fields
                (tree_eqb_fields tree_eqb) a)),
    Datatypes.is_true
      (@eqb_body tree tree_tag tree_fields_t tree_fields_t tree_fields
         (tree_eqb_fields tree_eqb) (tree_tag a) (tree_fields a) a) :=
    @eqb_body_refl tree tree_tag tree_fields_t tree_fields tree_construct
      tree_constructP (tree_eqb_fields tree_eqb)
    in
  let common0 :
    forall (a : forest)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on forest forest_tag forest_fields_t
                forest_fields (forest_eqb_fields forest_eqb) a)),
    Datatypes.is_true
      (@eqb_body forest forest_tag forest_fields_t forest_fields_t
         forest_fields (forest_eqb_fields forest_eqb) 
         (forest_tag a) (forest_fields a) a) :=
    @eqb_body_refl forest forest_tag forest_fields_t forest_fields
      forest_construct forest_constructP (forest_eqb_fields forest_eqb)
    in
  forest_induction (@eqb_refl_on tree tree_eqb)
    (@eqb_refl_on forest forest_eqb)
    (fun (x0 : forest) (_ : is_forest x0)
       (h : @eqb_refl_on forest forest_eqb x0) =>
     common (node x0) (eqb_refl_statementP (bcons (forest_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on tree tree_eqb (node x0))
    (common0 empty (eqb_refl_statementP bnil)
     :
     @eqb_refl_on forest forest_eqb empty)
    (fun (x0 : tree) (_ : is_tree x0) (h : @eqb_refl_on tree tree_eqb x0)
       (x1 : forest) (_ : is_forest x1)
       (h0 : @eqb_refl_on forest forest_eqb x1) =>
     common0 (cons x0 x1)
       (eqb_refl_statementP
          (bcons (forest_eqb x1 x1) (bcons (tree_eqb x0 x0) bnil)) h0 h)
     :
     @eqb_refl_on forest forest_eqb (cons x0 x1))
    x (is_forest_inhab x).
End MutualEqbCorrectExpected.

Module Type MutualEqbOKExpected.
  Include MutualEqbCorrectExpected.
  Definition tree_eqb_OK : forall x1 x2 : tree, reflect (@eq tree x1 x2) (tree_eqb x1 x2) :=
  @iffP2 tree tree_eqb tree_eqb_correct tree_eqb_refl.
  Definition forest_eqb_OK : forall x1 x2 : forest, reflect (@eq forest x1 x2) (forest_eqb x1 x2) :=
  @iffP2 forest forest_eqb forest_eqb_correct forest_eqb_refl.
  Definition tree_eqb_OK_sumbool : forall x y : tree, sumbool (@eq tree x y) (not (@eq tree x y)) :=
  reflect_dec tree tree_eqb tree_eqb_OK.
  Definition forest_eqb_OK_sumbool : forall x y : forest, sumbool (@eq forest x y) (not (@eq forest x y)) :=
  reflect_dec forest forest_eqb forest_eqb_OK.
End MutualEqbOKExpected.

Module Type MutualIsKExpected.
  Include MutualBase.
  Definition tree_isk_node : tree -> bool :=
  fun i : tree => match i with
                            | node _ => true
                            end.
  Definition forest_isk_empty : forest -> bool :=
  fun i : forest =>
  match i with
  | empty => true
  | cons _ _ => false
  end.
  Definition forest_isk_cons : forest -> bool :=
  fun i : forest =>
  match i with
  | empty => false
  | cons _ _ => true
  end.
End MutualIsKExpected.

Module Type MutualProjKExpected.
  Include MutualBase.
  Definition tree_getk_node1 : forest -> tree -> forest :=
  fun (_ : forest) (i : tree) =>
  match i with
  | node f0 => f0
  end.
  Definition forest_getk_cons1 : tree ->
       forest -> forest -> tree :=
  fun (t : tree) (_ i : forest) =>
  match i with
  | empty => t
  | cons t0 _ => t0
  end.
  Definition forest_getk_cons2 : tree ->
       forest -> forest -> forest :=
  fun (_ : tree) (f i : forest) =>
  match i with
  | empty => f
  | cons _ f0 => f0
  end.
End MutualProjKExpected.

Module Type MutualBcongrExpected.
  Include MutualProjKExpected.
  Definition tree_bcongr_node : forall (x y : forest) (b : bool),
       reflect (x = y) b ->
       reflect (node x = node y) b :=
  fun (x y : forest) (b : bool) (h : reflect (x = y) b) =>
  match
    h in reflect _ H
    return reflect (node x = node y) H
  with
  | ReflectT _ x0 =>
      match
        x0 in _ = H
        return reflect (node x = node H) true
      with
      | eq_refl => ReflectT (node x = node x) eq_refl
      end
  | ReflectF _ x0 =>
      ReflectF (node x = node y)
        (fun h0 : node x = node y =>
         x0
           (bcongr.eq_f tree forest
              (tree_getk_node1 x) (node x)
              (node y) h0))
  end.
  Definition forest_bcongr_empty : reflect (empty = empty) true :=
  ReflectT (empty = empty) eq_refl.
  Definition forest_bcongr_cons : forall (x y : tree) (b : bool),
       reflect (x = y) b ->
       forall (x0 y0 : forest) (b0 : bool),
       reflect (x0 = y0) b0 ->
       reflect (cons x x0 = cons y y0) (b && b0) :=
  fun (x y : tree) (b : bool) (h : reflect (x = y) b)
    (x0 y0 : forest) (b0 : bool) (h0 : reflect (x0 = y0) b0) =>
  match
    h in reflect _ H
    return reflect (cons x x0 = cons y y0) (H && b0)
  with
  | ReflectT _ x1 =>
      match
        x1 in _ = H
        return
          reflect (cons x x0 = cons H y0)
            (true && b0)
      with
      | eq_refl =>
          match
            h0 in reflect _ H
            return
              reflect (cons x x0 = cons x y0)
                (true && H)
          with
          | ReflectT _ x2 =>
              match
                x2 in _ = H
                return
                  reflect (cons x x0 = cons x H)
                    (true && true)
              with
              | eq_refl =>
                  ReflectT (cons x x0 = cons x x0)
                    eq_refl
              end
          | ReflectF _ x2 =>
              ReflectF (cons x x0 = cons x y0)
                (fun h1 : cons x x0 = cons x y0 =>
                 x2
                   (bcongr.eq_f forest forest
                      (forest_getk_cons2 x x0)
                      (cons x x0) (cons x y0) h1))
          end
      end
  | ReflectF _ x1 =>
      ReflectF (cons x x0 = cons y y0)
        (fun h1 : cons x x0 = cons y y0 =>
         x1
           (bcongr.eq_f forest tree
              (forest_getk_cons1 x x0) 
              (cons x x0) (cons y y0) h1))
  end.
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
  Definition ptree_map : forall A1 A2 : Type,
       (A1 -> A2) ->
       ptree A1 -> ptree A2 :=
  fun (A1 A2 : Type) (Af : A1 -> A2) =>
  fix ptree_map_rec (x : ptree A1) :
      ptree A2 :=
    match x with
    | pnode _ x0 f =>
        pnode A2 (Af x0) (pforest_map_rec f)
    end
  with pforest_map_rec (x : pforest A1) :
      pforest A2 :=
    match x with
    | pempty _ => pempty A2
    | pcons _ t f =>
        pcons A2 (ptree_map_rec t) (pforest_map_rec f)
    end
  for
  ptree_map_rec.
  Definition pforest_map : forall A1 A2 : Type,
       (A1 -> A2) ->
       pforest A1 -> pforest A2 :=
  fun (A1 A2 : Type) (Af : A1 -> A2) =>
  fix ptree_map_rec (x : ptree A1) :
      ptree A2 :=
    match x with
    | pnode _ x0 f =>
        pnode A2 (Af x0) (pforest_map_rec f)
    end
  with pforest_map_rec (x : pforest A1) :
      pforest A2 :=
    match x with
    | pempty _ => pempty A2
    | pcons _ t f =>
        pcons A2 (ptree_map_rec t) (pforest_map_rec f)
    end
  for
  pforest_map_rec.
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
  Definition reali_is_ptree : param1.reali_db ptree
         is_ptree :=
  @param1.store_reali _ _ ptree is_ptree.
  Definition reali_is_pforest : param1.reali_db pforest
         is_pforest :=
  @param1.store_reali _ _ pforest is_pforest.
  Definition reali_is_ptree_pnode : param1.reali_db pnode
         is_pnode :=
  @param1.store_reali _ _ pnode is_pnode.
  Definition reali_is_pforest_pempty : param1.reali_db pempty
         is_pempty :=
  @param1.store_reali _ _ pempty is_pempty.
  Definition reali_is_pforest_pcons : param1.reali_db pcons
         is_pcons :=
  @param1.store_reali _ _ pcons is_pcons.
End ParametrizedMutualParam1Expected.

Module Type ParametrizedMutualParam1CongrExpected.
  Include ParametrizedMutualParam1Expected.
  Definition congr_is_pnode : forall (x : Type) (p : x -> Type) (x0 : x) (p1 p2 : p x0),
       p1 = p2 ->
       forall (x1 : pforest x)
         (p3 p4 : is_pforest x p x1),
       p3 = p4 ->
       is_pnode x p x0 p1 x1 p3 =
       is_pnode x p x0 p2 x1 p4 :=
  fun (x : Type) (p : x -> Type) (x0 : x) (p1 p2 : p x0) (e : p1 = p2) =>
  match
    e in _ = i
    return
      (forall (x1 : pforest x)
         (p3 p4 : is_pforest x p x1),
       p3 = p4 ->
       is_pnode x p x0 p1 x1 p3 =
       is_pnode x p x0 i x1 p4)
  with
  | eq_refl =>
      fun (x1 : pforest x)
        (p3 p4 : is_pforest x p x1)
        (e0 : p3 = p4) =>
      match
        e0 in _ = i
        return
          is_pnode x p x0 p1 x1 p3 =
          is_pnode x p x0 p1 x1 i
      with
      | eq_refl => eq_refl
      end
  end.
  Definition congr_is_pempty : forall (x : Type) (p : x -> Type),
       is_pempty x p =
       is_pempty x p :=
  fun (x : Type) (p : x -> Type) => eq_refl.
  Definition congr_is_pcons : forall (x : Type) (p : x -> Type)
         (x0 : ptree x)
         (p1 p2 : is_ptree x p x0),
       p1 = p2 ->
       forall (x1 : pforest x)
         (p3 p4 : is_pforest x p x1),
       p3 = p4 ->
       is_pcons x p x0 p1 x1 p3 =
       is_pcons x p x0 p2 x1 p4 :=
  fun (x : Type) (p : x -> Type) (x0 : ptree x)
    (p1 p2 : is_ptree x p x0) 
    (e : p1 = p2) =>
  match
    e in _ = i
    return
      (forall (x1 : pforest x)
         (p3 p4 : is_pforest x p x1),
       p3 = p4 ->
       is_pcons x p x0 p1 x1 p3 =
       is_pcons x p x0 i x1 p4)
  with
  | eq_refl =>
      fun (x1 : pforest x)
        (p3 p4 : is_pforest x p x1)
        (e0 : p3 = p4) =>
      match
        e0 in _ = i
        return
          is_pcons x p x0 p1 x1 p3 =
          is_pcons x p x0 p1 x1 i
      with
      | eq_refl => eq_refl
      end
  end.
End ParametrizedMutualParam1CongrExpected.

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
  Definition param_ptree_R : param2.param_db ptree
         ptree ptree_R :=
  @param2.store_param _ _ _ ptree ptree ptree_R.
  Definition param_pforest_R : param2.param_db pforest
         pforest pforest_R :=
  @param2.store_param _ _ _ pforest pforest pforest_R.
  Definition param_pnode_R : param2.param_db pnode
         pnode pnode_R :=
  @param2.store_param _ _ _ pnode pnode pnode_R.
  Definition param_pempty_R : param2.param_db pempty
         pempty pempty_R :=
  @param2.store_param _ _ _ pempty pempty pempty_R.
  Definition param_pcons_R : param2.param_db pcons
         pcons pcons_R :=
  @param2.store_param _ _ _ pcons pcons pcons_R.
End ParametrizedMutualParam2Expected.

Module Type ParametrizedMutualTagExpected.
  Include ParametrizedMutualBase.
  Definition ptree_tag : forall A : Type, ptree A -> BinNums.positive :=
  fun (A : Type) (i : ptree A) =>
  match i with
  | pnode _ _ _ => BinNums.xH
  end.
  Definition pforest_tag : forall A : Type, pforest A -> BinNums.positive :=
  fun (A : Type) (i : pforest A) =>
  match i with
  | pempty _ => BinNums.xH
  | pcons _ _ _ => BinNums.xO BinNums.xH
  end.
End ParametrizedMutualTagExpected.

Module Type ParametrizedMutualFieldsExpected.
  Include ParametrizedMutualTagExpected.
  Universe box_ptree_pnode_u box_pforest_pempty_u box_pforest_pcons_u.
  Constraint Set < box_ptree_pnode_u.
  Constraint Set < box_pforest_pempty_u.
  Constraint Set < box_pforest_pcons_u.
  Record box_ptree_pnode (A : Type) : Type@{box_ptree_pnode_u} := Box_ptree_pnode {
    Box_ptree_pnode_0 : A;
    Box_ptree_pnode_1 : pforest A;
  }.
  Record box_pforest_pempty (A : Type) : Type@{box_pforest_pempty_u} := Box_pforest_pempty {}.
  Record box_pforest_pcons (A : Type) : Type@{box_pforest_pcons_u} := Box_pforest_pcons {
    Box_pforest_pcons_0 : ptree A;
    Box_pforest_pcons_1 : pforest A;
  }.
  Definition ptree_fields_t : Type -> BinNums.positive -> Type :=
  fun (p : Type) (_ : BinNums.positive) =>
  box_ptree_pnode p.
  Definition ptree_fields : forall (p : Type) (i : ptree p),
       ptree_fields_t p
         (ptree_tag p i) :=
  fun (p : Type) (i : ptree p) =>
  match
    i as i0
    return
      ptree_fields_t p
        (ptree_tag p i0)
  with
  | pnode _ x f =>
      {|
        Box_ptree_pnode_0 := x;
        Box_ptree_pnode_1 := f
      |}
  end.
  Definition ptree_construct : forall p : Type,
       BinNums.positive ->
       box_ptree_pnode p ->
       option (ptree p) :=
  fun (p : Type) (_ : BinNums.positive)
    (b : box_ptree_pnode p) =>
  match b with
  | {|
      Box_ptree_pnode_0 := Box_ptree_pnode_0;
      Box_ptree_pnode_1 := Box_ptree_pnode_1
    |} =>
      Some
        (pnode p Box_ptree_pnode_0 Box_ptree_pnode_1)
  end.
  Definition ptree_constructP : forall (A : Type) (i : ptree A),
       ptree_construct A
         (ptree_tag A i)
         (ptree_fields A i) =
       Some i :=
  fun (A : Type) (i : ptree A) =>
  match
    i as i0
    return
      ptree_construct A
        (ptree_tag A i0)
        (ptree_fields A i0) =
      Some i0
  with
  | pnode _ x f => eq_refl
  end.
  Definition pforest_fields_t : Type -> BinNums.positive -> Type :=
  fun (p : Type) (p0 : BinNums.positive) =>
  match p0 with
  | BinNums.xI _ => unit
  | BinNums.xO _ => box_pforest_pcons p
  | BinNums.xH => box_pforest_pempty p
  end.
  Definition pforest_fields : forall (p : Type) (i : pforest p),
       pforest_fields_t p
         (pforest_tag p i) :=
  fun (p : Type) (i : pforest p) =>
  match
    i as i0
    return
      pforest_fields_t p
        (pforest_tag p i0)
  with
  | pempty _ => Box_pforest_pempty p
  | pcons _ t f =>
      {|
        Box_pforest_pcons_0 := t;
        Box_pforest_pcons_1 := f
      |}
  end.
  Definition pforest_construct : forall (p : Type) (p0 : BinNums.positive),
       pforest_fields_t p p0 ->
       option (pforest p) :=
  fun (p : Type) (p0 : BinNums.positive) =>
  match
    p0 as i
    return
      pforest_fields_t p i ->
      option (pforest p)
  with
  | BinNums.xI _ => fun _ : unit => None
  | BinNums.xO _ =>
      fun b : box_pforest_pcons p =>
      match b with
      | {|
          Box_pforest_pcons_0 := Box_pforest_pcons_0;
          Box_pforest_pcons_1 := Box_pforest_pcons_1
        |} =>
          Some
            (pcons p Box_pforest_pcons_0
               Box_pforest_pcons_1)
      end
  | BinNums.xH =>
      fun _ : box_pforest_pempty p =>
      Some (pempty p)
  end.
  Definition pforest_constructP : forall (A : Type) (i : pforest A),
       pforest_construct A
         (pforest_tag A i)
         (pforest_fields A i) =
       Some i :=
  fun (A : Type) (i : pforest A) =>
  match
    i as i0
    return
      pforest_construct A
        (pforest_tag A i0)
        (pforest_fields A i0) =
      Some i0
  with
  | pempty _ => eq_refl
  | pcons _ t f => eq_refl
  end.
End ParametrizedMutualFieldsExpected.

Module Type ParametrizedMutualEqbExpected.
  Include ParametrizedMutualFieldsExpected.
  Definition ptree_eqb : forall a : Type,
       (a -> a -> bool) ->
       ptree a -> ptree a -> bool :=
  fun (a : Type) (eqA : a -> a -> bool) =>
  fix ptree (x1 x2 : ptree a) {struct x1} : bool :=
    match x1 with
    | pnode _ x f =>
        eqb_core_defs.eqb_body (tagB:=ptree_tag a)
          (fields_tA:=fun _ : BinNums.positive =>
                      box_ptree_pnode a)
          (fields_tB:=ptree_fields_t a)
          (ptree_fields a)
          (fun (_ : BinNums.positive)
             (a0 b : box_ptree_pnode a) =>
           match a0 with
           | {|
               Box_ptree_pnode_0 := Box_ptree_pnode_0;
               Box_ptree_pnode_1 := Box_ptree_pnode_1
             |} =>
               match b with
               | {|
                   Box_ptree_pnode_0 := Box_ptree_pnode_2;
                   Box_ptree_pnode_1 := Box_ptree_pnode_3
                 |} =>
                   (eqA Box_ptree_pnode_0 Box_ptree_pnode_2 &&
                    (pforest Box_ptree_pnode_1 Box_ptree_pnode_3 && true))%bool
               end
           end)
          (t1:=ptree_tag a
                 (pnode a x f))
          {|
            Box_ptree_pnode_0 := x;
            Box_ptree_pnode_1 := f
          |} x2
    end
  with pforest (x1 x2 : pforest a) {struct x1} : bool :=
    match x1 with
    | pempty _ =>
        eqb_core_defs.eqb_body (tagB:=pforest_tag a)
          (fields_tA:=pforest_fields_t a)
          (fields_tB:=pforest_fields_t a)
          (pforest_fields a)
          (fun x : BinNums.positive =>
           match
             x as i
             return
               pforest_fields_t a i ->
               pforest_fields_t a i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b : box_pforest_pcons a =>
               match a0 with
               | {|
                   Box_pforest_pcons_0 :=
                     Box_pforest_pcons_0;
                   Box_pforest_pcons_1 :=
                     Box_pforest_pcons_1
                 |} =>
                   match b with
                   | {|
                       Box_pforest_pcons_0 :=
                         Box_pforest_pcons_2;
                       Box_pforest_pcons_1 :=
                         Box_pforest_pcons_3
                     |} =>
                       (ptree Box_pforest_pcons_0 Box_pforest_pcons_2 &&
                        (pforest Box_pforest_pcons_1 Box_pforest_pcons_3 &&
                         true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_pforest_pempty a => true
           end)
          (t1:=pforest_tag a
                 (pempty a))
          (Box_pforest_pempty a) x2
    | pcons _ t f =>
        eqb_core_defs.eqb_body (tagB:=pforest_tag a)
          (fields_tA:=pforest_fields_t a)
          (fields_tB:=pforest_fields_t a)
          (pforest_fields a)
          (fun x : BinNums.positive =>
           match
             x as i
             return
               pforest_fields_t a i ->
               pforest_fields_t a i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b : box_pforest_pcons a =>
               match a0 with
               | {|
                   Box_pforest_pcons_0 :=
                     Box_pforest_pcons_0;
                   Box_pforest_pcons_1 :=
                     Box_pforest_pcons_1
                 |} =>
                   match b with
                   | {|
                       Box_pforest_pcons_0 :=
                         Box_pforest_pcons_2;
                       Box_pforest_pcons_1 :=
                         Box_pforest_pcons_3
                     |} =>
                       (ptree Box_pforest_pcons_0 Box_pforest_pcons_2 &&
                        (pforest Box_pforest_pcons_1 Box_pforest_pcons_3 &&
                         true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_pforest_pempty a => true
           end)
          (t1:=pforest_tag a
                 (pcons a t f))
          {|
            Box_pforest_pcons_0 := t;
            Box_pforest_pcons_1 := f
          |} x2
    end
  for
  ptree.
  Definition pforest_eqb : forall a : Type,
       (a -> a -> bool) ->
       pforest a ->
       pforest a -> bool :=
  fun (a : Type) (eqA : a -> a -> bool) =>
  fix ptree (x1 x2 : ptree a) {struct x1} : bool :=
    match x1 with
    | pnode _ x f =>
        eqb_core_defs.eqb_body (tagB:=ptree_tag a)
          (fields_tA:=fun _ : BinNums.positive =>
                      box_ptree_pnode a)
          (fields_tB:=ptree_fields_t a)
          (ptree_fields a)
          (fun (_ : BinNums.positive)
             (a0 b : box_ptree_pnode a) =>
           match a0 with
           | {|
               Box_ptree_pnode_0 := Box_ptree_pnode_0;
               Box_ptree_pnode_1 := Box_ptree_pnode_1
             |} =>
               match b with
               | {|
                   Box_ptree_pnode_0 := Box_ptree_pnode_2;
                   Box_ptree_pnode_1 := Box_ptree_pnode_3
                 |} =>
                   (eqA Box_ptree_pnode_0 Box_ptree_pnode_2 &&
                    (pforest Box_ptree_pnode_1 Box_ptree_pnode_3 && true))%bool
               end
           end)
          (t1:=ptree_tag a
                 (pnode a x f))
          {|
            Box_ptree_pnode_0 := x;
            Box_ptree_pnode_1 := f
          |} x2
    end
  with pforest (x1 x2 : pforest a) {struct x1} : bool :=
    match x1 with
    | pempty _ =>
        eqb_core_defs.eqb_body (tagB:=pforest_tag a)
          (fields_tA:=pforest_fields_t a)
          (fields_tB:=pforest_fields_t a)
          (pforest_fields a)
          (fun x : BinNums.positive =>
           match
             x as i
             return
               pforest_fields_t a i ->
               pforest_fields_t a i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b : box_pforest_pcons a =>
               match a0 with
               | {|
                   Box_pforest_pcons_0 :=
                     Box_pforest_pcons_0;
                   Box_pforest_pcons_1 :=
                     Box_pforest_pcons_1
                 |} =>
                   match b with
                   | {|
                       Box_pforest_pcons_0 :=
                         Box_pforest_pcons_2;
                       Box_pforest_pcons_1 :=
                         Box_pforest_pcons_3
                     |} =>
                       (ptree Box_pforest_pcons_0 Box_pforest_pcons_2 &&
                        (pforest Box_pforest_pcons_1 Box_pforest_pcons_3 &&
                         true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_pforest_pempty a => true
           end)
          (t1:=pforest_tag a
                 (pempty a))
          (Box_pforest_pempty a) x2
    | pcons _ t f =>
        eqb_core_defs.eqb_body (tagB:=pforest_tag a)
          (fields_tA:=pforest_fields_t a)
          (fields_tB:=pforest_fields_t a)
          (pforest_fields a)
          (fun x : BinNums.positive =>
           match
             x as i
             return
               pforest_fields_t a i ->
               pforest_fields_t a i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b : box_pforest_pcons a =>
               match a0 with
               | {|
                   Box_pforest_pcons_0 :=
                     Box_pforest_pcons_0;
                   Box_pforest_pcons_1 :=
                     Box_pforest_pcons_1
                 |} =>
                   match b with
                   | {|
                       Box_pforest_pcons_0 :=
                         Box_pforest_pcons_2;
                       Box_pforest_pcons_1 :=
                         Box_pforest_pcons_3
                     |} =>
                       (ptree Box_pforest_pcons_0 Box_pforest_pcons_2 &&
                        (pforest Box_pforest_pcons_1 Box_pforest_pcons_3 &&
                         true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_pforest_pempty a => true
           end)
          (t1:=pforest_tag a
                 (pcons a t f))
          {|
            Box_pforest_pcons_0 := t;
            Box_pforest_pcons_1 := f
          |} x2
    end
  for
  pforest.
  Definition ptree_eqb_fields : forall p : Type,
       (p -> p -> bool) ->
       (ptree p ->
        ptree p -> bool) ->
       BinNums.positive ->
       box_ptree_pnode p ->
       box_ptree_pnode p -> bool :=
  fun (p : Type) (eqp : p -> p -> bool)
    (_ : ptree p -> ptree p -> bool)
    (_ : BinNums.positive) (a b : box_ptree_pnode p) =>
  match a with
  | {|
      Box_ptree_pnode_0 := Box_ptree_pnode_0;
      Box_ptree_pnode_1 := Box_ptree_pnode_1
    |} =>
      match b with
      | {|
          Box_ptree_pnode_0 := Box_ptree_pnode_2;
          Box_ptree_pnode_1 := Box_ptree_pnode_3
        |} =>
          (eqp Box_ptree_pnode_0 Box_ptree_pnode_2 &&
           (pforest_eqb p eqp Box_ptree_pnode_1
              Box_ptree_pnode_3 &&
            true))%bool
      end
  end.
  Definition pforest_eqb_fields : forall p : Type,
       (p -> p -> bool) ->
       (pforest p ->
        pforest p -> bool) ->
       forall x : BinNums.positive,
       pforest_fields_t p x ->
       pforest_fields_t p x -> bool :=
  fun (p : Type) (eqp : p -> p -> bool)
    (rec : pforest p ->
           pforest p -> bool)
    (x : BinNums.positive) =>
  match
    x as i
    return
      pforest_fields_t p i ->
      pforest_fields_t p i -> bool
  with
  | BinNums.xI _ => fun _ _ : unit => true
  | BinNums.xO _ =>
      fun a b : box_pforest_pcons p =>
      match a with
      | {|
          Box_pforest_pcons_0 := Box_pforest_pcons_0;
          Box_pforest_pcons_1 := Box_pforest_pcons_1
        |} =>
          match b with
          | {|
              Box_pforest_pcons_0 := Box_pforest_pcons_2;
              Box_pforest_pcons_1 := Box_pforest_pcons_3
            |} =>
              (ptree_eqb p eqp Box_pforest_pcons_0
                 Box_pforest_pcons_2 &&
               (rec Box_pforest_pcons_1 Box_pforest_pcons_3 && true))%bool
          end
      end
  | BinNums.xH => fun _ _ : box_pforest_pempty p => true
  end.
End ParametrizedMutualEqbExpected.

Module Type ParametrizedMutualIsKExpected.
  Include ParametrizedMutualBase.
  Definition ptree_isk_pnode : forall A : Type, ptree A -> bool :=
  fun (A : Type) (i : ptree A) =>
  match i with
  | pnode _ _ _ => true
  end.
  Definition pforest_isk_pempty : forall A : Type, pforest A -> bool :=
  fun (A : Type) (i : pforest A) =>
  match i with
  | pempty _ => true
  | pcons _ _ _ => false
  end.
  Definition pforest_isk_pcons : forall A : Type, pforest A -> bool :=
  fun (A : Type) (i : pforest A) =>
  match i with
  | pempty _ => false
  | pcons _ _ _ => true
  end.
End ParametrizedMutualIsKExpected.

Module Type ParametrizedMutualProjKExpected.
  Include ParametrizedMutualBase.
  Definition ptree_getk_pnode1 : forall A : Type,
       A ->
       pforest A ->
       ptree A -> A :=
  fun (A : Type) (_ : A) (_ : pforest A)
    (i : ptree A) =>
  match i with
  | pnode _ x0 _ => x0
  end.
  Definition ptree_getk_pnode2 : forall A : Type,
       A ->
       pforest A ->
       ptree A -> pforest A :=
  fun (A : Type) (_ : A) (_ : pforest A)
    (i : ptree A) =>
  match i with
  | pnode _ _ f0 => f0
  end.
  Definition pforest_getk_pcons1 : forall A : Type,
       ptree A ->
       pforest A ->
       pforest A -> ptree A :=
  fun (A : Type) (t : ptree A)
    (_ i : pforest A) =>
  match i with
  | pempty _ => t
  | pcons _ t0 _ => t0
  end.
  Definition pforest_getk_pcons2 : forall A : Type,
       ptree A ->
       pforest A ->
       pforest A -> pforest A :=
  fun (A : Type) (_ : ptree A)
    (f i : pforest A) =>
  match i with
  | pempty _ => f
  | pcons _ _ f0 => f0
  end.
End ParametrizedMutualProjKExpected.

Module Type ParametrizedMutualBcongrExpected.
  Include ParametrizedMutualProjKExpected.
  Definition ptree_bcongr_pnode : forall (A : Type) (x y : A) (b : bool),
       reflect (x = y) b ->
       forall (x0 y0 : pforest A) (b0 : bool),
       reflect (x0 = y0) b0 ->
       reflect
         (pnode A x x0 =
          pnode A y y0)
         (b && b0) :=
  fun (A : Type) (x y : A) (b : bool) (h : reflect (x = y) b)
    (x0 y0 : pforest A) (b0 : bool)
    (h0 : reflect (x0 = y0) b0) =>
  match
    h in reflect _ H
    return
      reflect
        (pnode A x x0 =
         pnode A y y0)
        (H && b0)
  with
  | ReflectT _ x1 =>
      match
        x1 in _ = H
        return
          reflect
            (pnode A x x0 =
             pnode A H y0)
            (true && b0)
      with
      | eq_refl =>
          match
            h0 in reflect _ H
            return
              reflect
                (pnode A x x0 =
                 pnode A x y0)
                (true && H)
          with
          | ReflectT _ x2 =>
              match
                x2 in _ = H
                return
                  reflect
                    (pnode A x x0 =
                     pnode A x H)
                    (true && true)
              with
              | eq_refl =>
                  ReflectT
                    (pnode A x x0 =
                     pnode A x x0)
                    eq_refl
              end
          | ReflectF _ x2 =>
              ReflectF
                (pnode A x x0 =
                 pnode A x y0)
                (fun
                   h1 : pnode A x x0 =
                        pnode A x y0 =>
                 x2
                   (bcongr.eq_f (ptree A)
                      (pforest A)
                      (ptree_getk_pnode2 A x x0)
                      (pnode A x x0)
                      (pnode A x y0) h1))
          end
      end
  | ReflectF _ x1 =>
      ReflectF
        (pnode A x x0 =
         pnode A y y0)
        (fun
           h1 : pnode A x x0 =
                pnode A y y0 =>
         x1
           (bcongr.eq_f (ptree A) A
              (ptree_getk_pnode1 A x x0)
              (pnode A x x0)
              (pnode A y y0) h1))
  end.
  Definition pforest_bcongr_pempty : forall A : Type,
       reflect
         (pempty A =
          pempty A)
         true :=
  fun A : Type =>
  ReflectT
    (pempty A = pempty A)
    eq_refl.
  Definition pforest_bcongr_pcons : forall (A : Type) (x y : ptree A) (b : bool),
       reflect (x = y) b ->
       forall (x0 y0 : pforest A) (b0 : bool),
       reflect (x0 = y0) b0 ->
       reflect
         (pcons A x x0 =
          pcons A y y0)
         (b && b0) :=
  fun (A : Type) (x y : ptree A) 
    (b : bool) (h : reflect (x = y) b)
    (x0 y0 : pforest A) (b0 : bool)
    (h0 : reflect (x0 = y0) b0) =>
  match
    h in reflect _ H
    return
      reflect
        (pcons A x x0 =
         pcons A y y0)
        (H && b0)
  with
  | ReflectT _ x1 =>
      match
        x1 in _ = H
        return
          reflect
            (pcons A x x0 =
             pcons A H y0)
            (true && b0)
      with
      | eq_refl =>
          match
            h0 in reflect _ H
            return
              reflect
                (pcons A x x0 =
                 pcons A x y0)
                (true && H)
          with
          | ReflectT _ x2 =>
              match
                x2 in _ = H
                return
                  reflect
                    (pcons A x x0 =
                     pcons A x H)
                    (true && true)
              with
              | eq_refl =>
                  ReflectT
                    (pcons A x x0 =
                     pcons A x x0)
                    eq_refl
              end
          | ReflectF _ x2 =>
              ReflectF
                (pcons A x x0 =
                 pcons A x y0)
                (fun
                   h1 : pcons A x x0 =
                        pcons A x y0 =>
                 x2
                   (bcongr.eq_f (pforest A)
                      (pforest A)
                      (pforest_getk_pcons2 A x x0)
                      (pcons A x x0)
                      (pcons A x y0) h1))
          end
      end
  | ReflectF _ x1 =>
      ReflectF
        (pcons A x x0 =
         pcons A y y0)
        (fun
           h1 : pcons A x x0 =
                pcons A y y0 =>
         x1
           (bcongr.eq_f (pforest A)
              (ptree A)
              (pforest_getk_pcons1 A x x0)
              (pcons A x x0)
              (pcons A y y0) h1))
  end.
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
  Definition alpha_map : alpha -> alpha :=
  fun x : alpha => x.
  Definition beta_map : beta -> beta :=
  fun x : beta => x.
  Definition gamma_map : gamma -> gamma :=
  fun x : gamma => x.
End TripleMutualMapExpected.

Module Type TripleMutualEqbExpected.
  Include TripleMutualBase.
  Universe box_alpha_alpha0_u box_alpha_alpha1_u box_beta_beta0_u box_beta_beta1_u box_gamma_gamma0_u box_gamma_gamma1_u.
  Constraint Set < box_alpha_alpha0_u.
  Constraint Set < box_alpha_alpha1_u.
  Constraint Set < box_beta_beta0_u.
  Constraint Set < box_beta_beta1_u.
  Constraint Set < box_gamma_gamma0_u.
  Constraint Set < box_gamma_gamma1_u.
  Record box_alpha_alpha0 : Type@{box_alpha_alpha0_u} := Box_alpha_alpha0 {}.
  Record box_alpha_alpha1 : Type@{box_alpha_alpha1_u} := Box_alpha_alpha1 {
    Box_alpha_alpha1_0 : beta;
  }.
  Record box_beta_beta0 : Type@{box_beta_beta0_u} := Box_beta_beta0 {}.
  Record box_beta_beta1 : Type@{box_beta_beta1_u} := Box_beta_beta1 {
    Box_beta_beta1_0 : gamma;
  }.
  Record box_gamma_gamma0 : Type@{box_gamma_gamma0_u} := Box_gamma_gamma0 {}.
  Record box_gamma_gamma1 : Type@{box_gamma_gamma1_u} := Box_gamma_gamma1 {
    Box_gamma_gamma1_0 : alpha;
    Box_gamma_gamma1_1 : beta;
  }.
  Definition alpha_tag : alpha -> BinNums.positive :=
  fun i : alpha =>
  match i with
  | alpha0 => BinNums.xH
  | alpha1 _ => BinNums.xO BinNums.xH
  end.
  Definition beta_tag : beta -> BinNums.positive :=
  fun i : beta =>
  match i with
  | beta0 => BinNums.xH
  | beta1 _ => BinNums.xO BinNums.xH
  end.
  Definition gamma_tag : gamma -> BinNums.positive :=
  fun i : gamma =>
  match i with
  | gamma0 => BinNums.xH
  | gamma1 _ _ => BinNums.xO BinNums.xH
  end.
  Definition alpha_fields_t : BinNums.positive -> Type :=
  fun p : BinNums.positive =>
  match p with
  | BinNums.xI _ => unit
  | BinNums.xO _ => box_alpha_alpha1
  | BinNums.xH => box_alpha_alpha0
  end.
  Definition beta_fields_t : BinNums.positive -> Type :=
  fun p : BinNums.positive =>
  match p with
  | BinNums.xI _ => unit
  | BinNums.xO _ => box_beta_beta1
  | BinNums.xH => box_beta_beta0
  end.
  Definition gamma_fields_t : BinNums.positive -> Type :=
  fun p : BinNums.positive =>
  match p with
  | BinNums.xI _ => unit
  | BinNums.xO _ => box_gamma_gamma1
  | BinNums.xH => box_gamma_gamma0
  end.
  Definition alpha_fields : forall i : alpha,
       alpha_fields_t
         (alpha_tag i) :=
  fun i : alpha =>
  match
    i as i0
    return
      alpha_fields_t
        (alpha_tag i0)
  with
  | alpha0 =>
      Box_alpha_alpha0
  | alpha1 b =>
      {| Box_alpha_alpha1_0 := b |}
  end.
  Definition beta_fields : forall i : beta,
       beta_fields_t
         (beta_tag i) :=
  fun i : beta =>
  match
    i as i0
    return
      beta_fields_t
        (beta_tag i0)
  with
  | beta0 => Box_beta_beta0
  | beta1 g =>
      {| Box_beta_beta1_0 := g |}
  end.
  Definition gamma_fields : forall i : gamma,
       gamma_fields_t
         (gamma_tag i) :=
  fun i : gamma =>
  match
    i as i0
    return
      gamma_fields_t
        (gamma_tag i0)
  with
  | gamma0 =>
      Box_gamma_gamma0
  | gamma1 a b =>
      {|
        Box_gamma_gamma1_0 := a;
        Box_gamma_gamma1_1 := b
      |}
  end.
  Definition alpha_construct : forall p : BinNums.positive,
       alpha_fields_t p ->
       option alpha :=
  fun p : BinNums.positive =>
  match
    p as i
    return
      alpha_fields_t i ->
      option alpha
  with
  | BinNums.xI _ => fun _ : unit => None
  | BinNums.xO _ =>
      fun b : box_alpha_alpha1 =>
      match b with
      | {| Box_alpha_alpha1_0 := Box_alpha_alpha1_0 |} =>
          Some (alpha1 Box_alpha_alpha1_0)
      end
  | BinNums.xH =>
      fun _ : box_alpha_alpha0 =>
      Some alpha0
  end.
  Definition beta_construct : forall p : BinNums.positive,
       beta_fields_t p ->
       option beta :=
  fun p : BinNums.positive =>
  match
    p as i
    return
      beta_fields_t i ->
      option beta
  with
  | BinNums.xI _ => fun _ : unit => None
  | BinNums.xO _ =>
      fun b : box_beta_beta1 =>
      match b with
      | {| Box_beta_beta1_0 := Box_beta_beta1_0 |} =>
          Some (beta1 Box_beta_beta1_0)
      end
  | BinNums.xH =>
      fun _ : box_beta_beta0 =>
      Some beta0
  end.
  Definition gamma_construct : forall p : BinNums.positive,
       gamma_fields_t p ->
       option gamma :=
  fun p : BinNums.positive =>
  match
    p as i
    return
      gamma_fields_t i ->
      option gamma
  with
  | BinNums.xI _ => fun _ : unit => None
  | BinNums.xO _ =>
      fun b : box_gamma_gamma1 =>
      match b with
      | {|
          Box_gamma_gamma1_0 := Box_gamma_gamma1_0;
          Box_gamma_gamma1_1 := Box_gamma_gamma1_1
        |} =>
          Some
            (gamma1 Box_gamma_gamma1_0
               Box_gamma_gamma1_1)
      end
  | BinNums.xH =>
      fun _ : box_gamma_gamma0 =>
      Some gamma0
  end.
  Definition alpha_constructP : forall i : alpha,
       alpha_construct
         (alpha_tag i)
         (alpha_fields i) =
       Some i :=
  fun i : alpha =>
  match
    i as i0
    return
      alpha_construct
        (alpha_tag i0)
        (alpha_fields i0) =
      Some i0
  with
  | alpha0 => eq_refl
  | alpha1 b => eq_refl
  end.
  Definition beta_constructP : forall i : beta,
       beta_construct
         (beta_tag i)
         (beta_fields i) =
       Some i :=
  fun i : beta =>
  match
    i as i0
    return
      beta_construct
        (beta_tag i0)
        (beta_fields i0) =
      Some i0
  with
  | beta0 => eq_refl
  | beta1 g => eq_refl
  end.
  Definition gamma_constructP : forall i : gamma,
       gamma_construct
         (gamma_tag i)
         (gamma_fields i) =
       Some i :=
  fun i : gamma =>
  match
    i as i0
    return
      gamma_construct
        (gamma_tag i0)
        (gamma_fields i0) =
      Some i0
  with
  | gamma0 => eq_refl
  | gamma1 a b => eq_refl
  end.
  Definition alpha_eqb : alpha -> alpha -> bool :=
  fix alpha (x1 x2 : alpha) {struct x1} : bool :=
    match x1 with
    | alpha0 =>
        eqb_core_defs.eqb_body (tagB:=alpha_tag)
          (fields_tA:=alpha_fields_t)
          (fields_tB:=alpha_fields_t)
          alpha_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               alpha_fields_t i ->
               alpha_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_alpha_alpha1 =>
               match a with
               | {|
                   Box_alpha_alpha1_0 :=
                     Box_alpha_alpha1_0
                 |} =>
                   match b with
                   | {|
                       Box_alpha_alpha1_0 :=
                         Box_alpha_alpha1_1
                     |} =>
                       (beta Box_alpha_alpha1_0 Box_alpha_alpha1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_alpha_alpha0 => true
           end)
          (t1:=alpha_tag
                 alpha0)
          Box_alpha_alpha0 x2
    | alpha1 b =>
        eqb_core_defs.eqb_body (tagB:=alpha_tag)
          (fields_tA:=alpha_fields_t)
          (fields_tB:=alpha_fields_t)
          alpha_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               alpha_fields_t i ->
               alpha_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b0 : box_alpha_alpha1 =>
               match a with
               | {|
                   Box_alpha_alpha1_0 :=
                     Box_alpha_alpha1_0
                 |} =>
                   match b0 with
                   | {|
                       Box_alpha_alpha1_0 :=
                         Box_alpha_alpha1_1
                     |} =>
                       (beta Box_alpha_alpha1_0 Box_alpha_alpha1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_alpha_alpha0 => true
           end)
          (t1:=alpha_tag
                 (alpha1 b))
          {| Box_alpha_alpha1_0 := b |} x2
    end
  with beta (x1 x2 : beta) {struct x1} : bool :=
    match x1 with
    | beta0 =>
        eqb_core_defs.eqb_body (tagB:=beta_tag)
          (fields_tA:=beta_fields_t)
          (fields_tB:=beta_fields_t)
          beta_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               beta_fields_t i ->
               beta_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_beta_beta1 =>
               match a with
               | {|
                   Box_beta_beta1_0 :=
                     Box_beta_beta1_0
                 |} =>
                   match b with
                   | {|
                       Box_beta_beta1_0 :=
                         Box_beta_beta1_1
                     |} =>
                       (gamma Box_beta_beta1_0 Box_beta_beta1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_beta_beta0 => true
           end)
          (t1:=beta_tag beta0)
          Box_beta_beta0 x2
    | beta1 g =>
        eqb_core_defs.eqb_body (tagB:=beta_tag)
          (fields_tA:=beta_fields_t)
          (fields_tB:=beta_fields_t)
          beta_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               beta_fields_t i ->
               beta_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_beta_beta1 =>
               match a with
               | {|
                   Box_beta_beta1_0 :=
                     Box_beta_beta1_0
                 |} =>
                   match b with
                   | {|
                       Box_beta_beta1_0 :=
                         Box_beta_beta1_1
                     |} =>
                       (gamma Box_beta_beta1_0 Box_beta_beta1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_beta_beta0 => true
           end)
          (t1:=beta_tag
                 (beta1 g))
          {| Box_beta_beta1_0 := g |} x2
    end
  with gamma (x1 x2 : gamma) {struct x1} : bool :=
    match x1 with
    | gamma0 =>
        eqb_core_defs.eqb_body (tagB:=gamma_tag)
          (fields_tA:=gamma_fields_t)
          (fields_tB:=gamma_fields_t)
          gamma_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               gamma_fields_t i ->
               gamma_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_gamma_gamma1 =>
               match a with
               | {|
                   Box_gamma_gamma1_0 :=
                     Box_gamma_gamma1_0;
                   Box_gamma_gamma1_1 :=
                     Box_gamma_gamma1_1
                 |} =>
                   match b with
                   | {|
                       Box_gamma_gamma1_0 :=
                         Box_gamma_gamma1_2;
                       Box_gamma_gamma1_1 :=
                         Box_gamma_gamma1_3
                     |} =>
                       (alpha Box_gamma_gamma1_0 Box_gamma_gamma1_2 &&
                        (beta Box_gamma_gamma1_1 Box_gamma_gamma1_3 && true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_gamma_gamma0 => true
           end)
          (t1:=gamma_tag
                 gamma0)
          Box_gamma_gamma0 x2
    | gamma1 a b =>
        eqb_core_defs.eqb_body (tagB:=gamma_tag)
          (fields_tA:=gamma_fields_t)
          (fields_tB:=gamma_fields_t)
          gamma_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               gamma_fields_t i ->
               gamma_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b0 : box_gamma_gamma1 =>
               match a0 with
               | {|
                   Box_gamma_gamma1_0 :=
                     Box_gamma_gamma1_0;
                   Box_gamma_gamma1_1 :=
                     Box_gamma_gamma1_1
                 |} =>
                   match b0 with
                   | {|
                       Box_gamma_gamma1_0 :=
                         Box_gamma_gamma1_2;
                       Box_gamma_gamma1_1 :=
                         Box_gamma_gamma1_3
                     |} =>
                       (alpha Box_gamma_gamma1_0 Box_gamma_gamma1_2 &&
                        (beta Box_gamma_gamma1_1 Box_gamma_gamma1_3 && true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_gamma_gamma0 => true
           end)
          (t1:=gamma_tag
                 (gamma1 a b))
          {|
            Box_gamma_gamma1_0 := a;
            Box_gamma_gamma1_1 := b
          |} x2
    end
  for
  alpha.
  Definition beta_eqb : beta -> beta -> bool :=
  fix alpha (x1 x2 : alpha) {struct x1} : bool :=
    match x1 with
    | alpha0 =>
        eqb_core_defs.eqb_body (tagB:=alpha_tag)
          (fields_tA:=alpha_fields_t)
          (fields_tB:=alpha_fields_t)
          alpha_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               alpha_fields_t i ->
               alpha_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_alpha_alpha1 =>
               match a with
               | {|
                   Box_alpha_alpha1_0 :=
                     Box_alpha_alpha1_0
                 |} =>
                   match b with
                   | {|
                       Box_alpha_alpha1_0 :=
                         Box_alpha_alpha1_1
                     |} =>
                       (beta Box_alpha_alpha1_0 Box_alpha_alpha1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_alpha_alpha0 => true
           end)
          (t1:=alpha_tag
                 alpha0)
          Box_alpha_alpha0 x2
    | alpha1 b =>
        eqb_core_defs.eqb_body (tagB:=alpha_tag)
          (fields_tA:=alpha_fields_t)
          (fields_tB:=alpha_fields_t)
          alpha_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               alpha_fields_t i ->
               alpha_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b0 : box_alpha_alpha1 =>
               match a with
               | {|
                   Box_alpha_alpha1_0 :=
                     Box_alpha_alpha1_0
                 |} =>
                   match b0 with
                   | {|
                       Box_alpha_alpha1_0 :=
                         Box_alpha_alpha1_1
                     |} =>
                       (beta Box_alpha_alpha1_0 Box_alpha_alpha1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_alpha_alpha0 => true
           end)
          (t1:=alpha_tag
                 (alpha1 b))
          {| Box_alpha_alpha1_0 := b |} x2
    end
  with beta (x1 x2 : beta) {struct x1} : bool :=
    match x1 with
    | beta0 =>
        eqb_core_defs.eqb_body (tagB:=beta_tag)
          (fields_tA:=beta_fields_t)
          (fields_tB:=beta_fields_t)
          beta_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               beta_fields_t i ->
               beta_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_beta_beta1 =>
               match a with
               | {|
                   Box_beta_beta1_0 :=
                     Box_beta_beta1_0
                 |} =>
                   match b with
                   | {|
                       Box_beta_beta1_0 :=
                         Box_beta_beta1_1
                     |} =>
                       (gamma Box_beta_beta1_0 Box_beta_beta1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_beta_beta0 => true
           end)
          (t1:=beta_tag beta0)
          Box_beta_beta0 x2
    | beta1 g =>
        eqb_core_defs.eqb_body (tagB:=beta_tag)
          (fields_tA:=beta_fields_t)
          (fields_tB:=beta_fields_t)
          beta_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               beta_fields_t i ->
               beta_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_beta_beta1 =>
               match a with
               | {|
                   Box_beta_beta1_0 :=
                     Box_beta_beta1_0
                 |} =>
                   match b with
                   | {|
                       Box_beta_beta1_0 :=
                         Box_beta_beta1_1
                     |} =>
                       (gamma Box_beta_beta1_0 Box_beta_beta1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_beta_beta0 => true
           end)
          (t1:=beta_tag
                 (beta1 g))
          {| Box_beta_beta1_0 := g |} x2
    end
  with gamma (x1 x2 : gamma) {struct x1} : bool :=
    match x1 with
    | gamma0 =>
        eqb_core_defs.eqb_body (tagB:=gamma_tag)
          (fields_tA:=gamma_fields_t)
          (fields_tB:=gamma_fields_t)
          gamma_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               gamma_fields_t i ->
               gamma_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_gamma_gamma1 =>
               match a with
               | {|
                   Box_gamma_gamma1_0 :=
                     Box_gamma_gamma1_0;
                   Box_gamma_gamma1_1 :=
                     Box_gamma_gamma1_1
                 |} =>
                   match b with
                   | {|
                       Box_gamma_gamma1_0 :=
                         Box_gamma_gamma1_2;
                       Box_gamma_gamma1_1 :=
                         Box_gamma_gamma1_3
                     |} =>
                       (alpha Box_gamma_gamma1_0 Box_gamma_gamma1_2 &&
                        (beta Box_gamma_gamma1_1 Box_gamma_gamma1_3 && true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_gamma_gamma0 => true
           end)
          (t1:=gamma_tag
                 gamma0)
          Box_gamma_gamma0 x2
    | gamma1 a b =>
        eqb_core_defs.eqb_body (tagB:=gamma_tag)
          (fields_tA:=gamma_fields_t)
          (fields_tB:=gamma_fields_t)
          gamma_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               gamma_fields_t i ->
               gamma_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b0 : box_gamma_gamma1 =>
               match a0 with
               | {|
                   Box_gamma_gamma1_0 :=
                     Box_gamma_gamma1_0;
                   Box_gamma_gamma1_1 :=
                     Box_gamma_gamma1_1
                 |} =>
                   match b0 with
                   | {|
                       Box_gamma_gamma1_0 :=
                         Box_gamma_gamma1_2;
                       Box_gamma_gamma1_1 :=
                         Box_gamma_gamma1_3
                     |} =>
                       (alpha Box_gamma_gamma1_0 Box_gamma_gamma1_2 &&
                        (beta Box_gamma_gamma1_1 Box_gamma_gamma1_3 && true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_gamma_gamma0 => true
           end)
          (t1:=gamma_tag
                 (gamma1 a b))
          {|
            Box_gamma_gamma1_0 := a;
            Box_gamma_gamma1_1 := b
          |} x2
    end
  for
  beta.
  Definition gamma_eqb : gamma ->
       gamma -> bool :=
  fix alpha (x1 x2 : alpha) {struct x1} : bool :=
    match x1 with
    | alpha0 =>
        eqb_core_defs.eqb_body (tagB:=alpha_tag)
          (fields_tA:=alpha_fields_t)
          (fields_tB:=alpha_fields_t)
          alpha_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               alpha_fields_t i ->
               alpha_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_alpha_alpha1 =>
               match a with
               | {|
                   Box_alpha_alpha1_0 :=
                     Box_alpha_alpha1_0
                 |} =>
                   match b with
                   | {|
                       Box_alpha_alpha1_0 :=
                         Box_alpha_alpha1_1
                     |} =>
                       (beta Box_alpha_alpha1_0 Box_alpha_alpha1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_alpha_alpha0 => true
           end)
          (t1:=alpha_tag
                 alpha0)
          Box_alpha_alpha0 x2
    | alpha1 b =>
        eqb_core_defs.eqb_body (tagB:=alpha_tag)
          (fields_tA:=alpha_fields_t)
          (fields_tB:=alpha_fields_t)
          alpha_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               alpha_fields_t i ->
               alpha_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b0 : box_alpha_alpha1 =>
               match a with
               | {|
                   Box_alpha_alpha1_0 :=
                     Box_alpha_alpha1_0
                 |} =>
                   match b0 with
                   | {|
                       Box_alpha_alpha1_0 :=
                         Box_alpha_alpha1_1
                     |} =>
                       (beta Box_alpha_alpha1_0 Box_alpha_alpha1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_alpha_alpha0 => true
           end)
          (t1:=alpha_tag
                 (alpha1 b))
          {| Box_alpha_alpha1_0 := b |} x2
    end
  with beta (x1 x2 : beta) {struct x1} : bool :=
    match x1 with
    | beta0 =>
        eqb_core_defs.eqb_body (tagB:=beta_tag)
          (fields_tA:=beta_fields_t)
          (fields_tB:=beta_fields_t)
          beta_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               beta_fields_t i ->
               beta_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_beta_beta1 =>
               match a with
               | {|
                   Box_beta_beta1_0 :=
                     Box_beta_beta1_0
                 |} =>
                   match b with
                   | {|
                       Box_beta_beta1_0 :=
                         Box_beta_beta1_1
                     |} =>
                       (gamma Box_beta_beta1_0 Box_beta_beta1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_beta_beta0 => true
           end)
          (t1:=beta_tag beta0)
          Box_beta_beta0 x2
    | beta1 g =>
        eqb_core_defs.eqb_body (tagB:=beta_tag)
          (fields_tA:=beta_fields_t)
          (fields_tB:=beta_fields_t)
          beta_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               beta_fields_t i ->
               beta_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_beta_beta1 =>
               match a with
               | {|
                   Box_beta_beta1_0 :=
                     Box_beta_beta1_0
                 |} =>
                   match b with
                   | {|
                       Box_beta_beta1_0 :=
                         Box_beta_beta1_1
                     |} =>
                       (gamma Box_beta_beta1_0 Box_beta_beta1_1 && true)%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_beta_beta0 => true
           end)
          (t1:=beta_tag
                 (beta1 g))
          {| Box_beta_beta1_0 := g |} x2
    end
  with gamma (x1 x2 : gamma) {struct x1} : bool :=
    match x1 with
    | gamma0 =>
        eqb_core_defs.eqb_body (tagB:=gamma_tag)
          (fields_tA:=gamma_fields_t)
          (fields_tB:=gamma_fields_t)
          gamma_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               gamma_fields_t i ->
               gamma_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a b : box_gamma_gamma1 =>
               match a with
               | {|
                   Box_gamma_gamma1_0 :=
                     Box_gamma_gamma1_0;
                   Box_gamma_gamma1_1 :=
                     Box_gamma_gamma1_1
                 |} =>
                   match b with
                   | {|
                       Box_gamma_gamma1_0 :=
                         Box_gamma_gamma1_2;
                       Box_gamma_gamma1_1 :=
                         Box_gamma_gamma1_3
                     |} =>
                       (alpha Box_gamma_gamma1_0 Box_gamma_gamma1_2 &&
                        (beta Box_gamma_gamma1_1 Box_gamma_gamma1_3 && true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_gamma_gamma0 => true
           end)
          (t1:=gamma_tag
                 gamma0)
          Box_gamma_gamma0 x2
    | gamma1 a b =>
        eqb_core_defs.eqb_body (tagB:=gamma_tag)
          (fields_tA:=gamma_fields_t)
          (fields_tB:=gamma_fields_t)
          gamma_fields
          (fun x : BinNums.positive =>
           match
             x as i
             return
               gamma_fields_t i ->
               gamma_fields_t i -> bool
           with
           | BinNums.xI _ => fun _ _ : unit => true
           | BinNums.xO _ =>
               fun a0 b0 : box_gamma_gamma1 =>
               match a0 with
               | {|
                   Box_gamma_gamma1_0 :=
                     Box_gamma_gamma1_0;
                   Box_gamma_gamma1_1 :=
                     Box_gamma_gamma1_1
                 |} =>
                   match b0 with
                   | {|
                       Box_gamma_gamma1_0 :=
                         Box_gamma_gamma1_2;
                       Box_gamma_gamma1_1 :=
                         Box_gamma_gamma1_3
                     |} =>
                       (alpha Box_gamma_gamma1_0 Box_gamma_gamma1_2 &&
                        (beta Box_gamma_gamma1_1 Box_gamma_gamma1_3 && true))%bool
                   end
               end
           | BinNums.xH =>
               fun _ _ : box_gamma_gamma0 => true
           end)
          (t1:=gamma_tag
                 (gamma1 a b))
          {|
            Box_gamma_gamma1_0 := a;
            Box_gamma_gamma1_1 := b
          |} x2
    end
  for
  gamma.
  Definition alpha_eqb_fields : (alpha ->
        alpha -> bool) ->
       forall x : BinNums.positive,
       alpha_fields_t x ->
       alpha_fields_t x -> bool :=
  fun
    (_ : alpha ->
         alpha -> bool)
    (x : BinNums.positive) =>
  match
    x as i
    return
      alpha_fields_t i ->
      alpha_fields_t i -> bool
  with
  | BinNums.xI _ => fun _ _ : unit => true
  | BinNums.xO _ =>
      fun a b : box_alpha_alpha1 =>
      match a with
      | {| Box_alpha_alpha1_0 := Box_alpha_alpha1_0 |} =>
          match b with
          | {|
              Box_alpha_alpha1_0 := Box_alpha_alpha1_1
            |} =>
              (beta_eqb Box_alpha_alpha1_0
                 Box_alpha_alpha1_1 &&
               true)%bool
          end
      end
  | BinNums.xH => fun _ _ : box_alpha_alpha0 => true
  end.
  Definition beta_eqb_fields : (beta ->
        beta -> bool) ->
       forall x : BinNums.positive,
       beta_fields_t x ->
       beta_fields_t x -> bool :=
  fun
    (_ : beta -> beta -> bool)
    (x : BinNums.positive) =>
  match
    x as i
    return
      beta_fields_t i ->
      beta_fields_t i -> bool
  with
  | BinNums.xI _ => fun _ _ : unit => true
  | BinNums.xO _ =>
      fun a b : box_beta_beta1 =>
      match a with
      | {| Box_beta_beta1_0 := Box_beta_beta1_0 |} =>
          match b with
          | {| Box_beta_beta1_0 := Box_beta_beta1_1 |} =>
              (gamma_eqb Box_beta_beta1_0
                 Box_beta_beta1_1 &&
               true)%bool
          end
      end
  | BinNums.xH => fun _ _ : box_beta_beta0 => true
  end.
  Definition gamma_eqb_fields : (gamma ->
        gamma -> bool) ->
       forall x : BinNums.positive,
       gamma_fields_t x ->
       gamma_fields_t x -> bool :=
  fun
    (_ : gamma ->
         gamma -> bool)
    (x : BinNums.positive) =>
  match
    x as i
    return
      gamma_fields_t i ->
      gamma_fields_t i -> bool
  with
  | BinNums.xI _ => fun _ _ : unit => true
  | BinNums.xO _ =>
      fun a b : box_gamma_gamma1 =>
      match a with
      | {|
          Box_gamma_gamma1_0 := Box_gamma_gamma1_0;
          Box_gamma_gamma1_1 := Box_gamma_gamma1_1
        |} =>
          match b with
          | {|
              Box_gamma_gamma1_0 := Box_gamma_gamma1_2;
              Box_gamma_gamma1_1 := Box_gamma_gamma1_3
            |} =>
              (alpha_eqb Box_gamma_gamma1_0
                 Box_gamma_gamma1_2 &&
               (beta_eqb Box_gamma_gamma1_1
                  Box_gamma_gamma1_3 &&
                true))%bool
          end
      end
  | BinNums.xH => fun _ _ : box_gamma_gamma0 => true
  end.
End TripleMutualEqbExpected.

Module Type TripleMutualEqbOKExpected.
  Include TripleMutualEqbExpected.
  Universe alpha_reali_u beta_reali_u gamma_reali_u.
  Constraint Set < alpha_reali_u.
  Constraint Set < beta_reali_u.
  Constraint Set < gamma_reali_u.
  Inductive is_alpha : alpha -> Type@{alpha_reali_u} :=
  | is_alpha0 : is_alpha alpha0
  | is_alpha1 (b : beta) (Pb : is_beta b) : is_alpha (alpha1 b)
  with is_beta : beta -> Type@{beta_reali_u} :=
  | is_beta0 : is_beta beta0
  | is_beta1 (g : gamma) (Pg : is_gamma g) : is_beta (beta1 g)
  with is_gamma : gamma -> Type@{gamma_reali_u} :=
  | is_gamma0 : is_gamma gamma0
  | is_gamma1 (a : alpha) (Pa : is_alpha a)
      (b : beta) (Pb : is_beta b) : is_gamma (gamma1 a b).
  Definition is_alpha_inhab : forall x : alpha, is_alpha x :=
  fix is_alpha_inhab_rec (x : alpha) : is_alpha x :=
    match x as i return is_alpha i with
    | alpha0 => is_alpha0
    | alpha1 b => is_alpha1 b (is_beta_inhab_rec b)
    end
  with is_beta_inhab_rec (x : beta) : is_beta x :=
    match x as i return is_beta i with
    | beta0 => is_beta0
    | beta1 g => is_beta1 g (is_gamma_inhab_rec g)
    end
  with is_gamma_inhab_rec (x : gamma) : is_gamma x :=
    match x as i return is_gamma i with
    | gamma0 => is_gamma0
    | gamma1 a b => is_gamma1 a (is_alpha_inhab_rec a) b (is_beta_inhab_rec b)
    end
  for
  is_alpha_inhab_rec.
  Definition is_beta_inhab : forall x : beta, is_beta x :=
  fix is_alpha_inhab_rec (x : alpha) : is_alpha x :=
    match x as i return is_alpha i with
    | alpha0 => is_alpha0
    | alpha1 b => is_alpha1 b (is_beta_inhab_rec b)
    end
  with is_beta_inhab_rec (x : beta) : is_beta x :=
    match x as i return is_beta i with
    | beta0 => is_beta0
    | beta1 g => is_beta1 g (is_gamma_inhab_rec g)
    end
  with is_gamma_inhab_rec (x : gamma) : is_gamma x :=
    match x as i return is_gamma i with
    | gamma0 => is_gamma0
    | gamma1 a b => is_gamma1 a (is_alpha_inhab_rec a) b (is_beta_inhab_rec b)
    end
  for
  is_beta_inhab_rec.
  Definition is_gamma_inhab : forall x : gamma, is_gamma x :=
  fix is_alpha_inhab_rec (x : alpha) : is_alpha x :=
    match x as i return is_alpha i with
    | alpha0 => is_alpha0
    | alpha1 b => is_alpha1 b (is_beta_inhab_rec b)
    end
  with is_beta_inhab_rec (x : beta) : is_beta x :=
    match x as i return is_beta i with
    | beta0 => is_beta0
    | beta1 g => is_beta1 g (is_gamma_inhab_rec g)
    end
  with is_gamma_inhab_rec (x : gamma) : is_gamma x :=
    match x as i return is_gamma i with
    | gamma0 => is_gamma0
    | gamma1 a b => is_gamma1 a (is_alpha_inhab_rec a) b (is_beta_inhab_rec b)
    end
  for
  is_gamma_inhab_rec.
  Definition alpha_induction : forall (P : forall _ : alpha, Type) (P0 : forall _ : beta, Type)
         (P1 : forall _ : gamma, Type) (_ : P alpha0)
         (_ : forall (b : beta) (_ : is_beta b) (_ : P0 b), P (alpha1 b))
         (_ : P0 beta0)
         (_ : forall (g : gamma) (_ : is_gamma g) (_ : P1 g), P0 (beta1 g))
         (_ : P1 gamma0)
         (_ : forall (a : alpha) (_ : is_alpha a) 
                (_ : P a) (b : beta) (_ : is_beta b) 
                (_ : P0 b),
              P1 (gamma1 a b))
         (s1 : alpha) (_ : is_alpha s1),
       P s1 :=
  fun (P : forall _ : alpha, Type) (P0 : forall _ : beta, Type)
    (P1 : forall _ : gamma, Type) (His_alpha0 : P alpha0)
    (His_alpha1 : forall (b : beta) (_ : is_beta b) (_ : P0 b), P (alpha1 b))
    (His_beta0 : P0 beta0)
    (His_beta1 : forall (g : gamma) (_ : is_gamma g) (_ : P1 g), P0 (beta1 g))
    (His_gamma0 : P1 gamma0)
    (His_gamma1 : forall (a : alpha) (_ : is_alpha a) 
                    (_ : P a) (b : beta) (_ : is_beta b) 
                    (_ : P0 b),
                  P1 (gamma1 a b)) =>
  fix is_alpha_induction_rec (s1 : alpha) (H : is_alpha s1) {struct H} :
      P s1 :=
    match H in is_alpha s2 return P s2 with
    | is_alpha0 => His_alpha0
    | is_alpha1 b Pb => His_alpha1 b Pb (is_beta_induction_rec b Pb)
    end
  with is_beta_induction_rec (s1 : beta) (H : is_beta s1) {struct H} : P0 s1 :=
    match H in is_beta s2 return P0 s2 with
    | is_beta0 => His_beta0
    | is_beta1 g Pg => His_beta1 g Pg (is_gamma_induction_rec g Pg)
    end
  with is_gamma_induction_rec (s1 : gamma) (H : is_gamma s1) {struct H} :
      P1 s1 :=
    match H in is_gamma s2 return P1 s2 with
    | is_gamma0 => His_gamma0
    | is_gamma1 a Pa b Pb =>
        His_gamma1 a Pa (is_alpha_induction_rec a Pa) b Pb
          (is_beta_induction_rec b Pb)
    end
  for
  is_alpha_induction_rec.
  Definition beta_induction : forall (P : forall _ : alpha, Type) (P0 : forall _ : beta, Type)
         (P1 : forall _ : gamma, Type) (_ : P alpha0)
         (_ : forall (b : beta) (_ : is_beta b) (_ : P0 b), P (alpha1 b))
         (_ : P0 beta0)
         (_ : forall (g : gamma) (_ : is_gamma g) (_ : P1 g), P0 (beta1 g))
         (_ : P1 gamma0)
         (_ : forall (a : alpha) (_ : is_alpha a) 
                (_ : P a) (b : beta) (_ : is_beta b) 
                (_ : P0 b),
              P1 (gamma1 a b))
         (s1 : beta) (_ : is_beta s1),
       P0 s1 :=
  fun (P : forall _ : alpha, Type) (P0 : forall _ : beta, Type)
    (P1 : forall _ : gamma, Type) (His_alpha0 : P alpha0)
    (His_alpha1 : forall (b : beta) (_ : is_beta b) (_ : P0 b), P (alpha1 b))
    (His_beta0 : P0 beta0)
    (His_beta1 : forall (g : gamma) (_ : is_gamma g) (_ : P1 g), P0 (beta1 g))
    (His_gamma0 : P1 gamma0)
    (His_gamma1 : forall (a : alpha) (_ : is_alpha a) 
                    (_ : P a) (b : beta) (_ : is_beta b) 
                    (_ : P0 b),
                  P1 (gamma1 a b)) =>
  fix is_alpha_induction_rec (s1 : alpha) (H : is_alpha s1) {struct H} :
      P s1 :=
    match H in is_alpha s2 return P s2 with
    | is_alpha0 => His_alpha0
    | is_alpha1 b Pb => His_alpha1 b Pb (is_beta_induction_rec b Pb)
    end
  with is_beta_induction_rec (s1 : beta) (H : is_beta s1) {struct H} : P0 s1 :=
    match H in is_beta s2 return P0 s2 with
    | is_beta0 => His_beta0
    | is_beta1 g Pg => His_beta1 g Pg (is_gamma_induction_rec g Pg)
    end
  with is_gamma_induction_rec (s1 : gamma) (H : is_gamma s1) {struct H} :
      P1 s1 :=
    match H in is_gamma s2 return P1 s2 with
    | is_gamma0 => His_gamma0
    | is_gamma1 a Pa b Pb =>
        His_gamma1 a Pa (is_alpha_induction_rec a Pa) b Pb
          (is_beta_induction_rec b Pb)
    end
  for
  is_beta_induction_rec.
  Definition gamma_induction : forall (P : forall _ : alpha, Type) (P0 : forall _ : beta, Type)
         (P1 : forall _ : gamma, Type) (_ : P alpha0)
         (_ : forall (b : beta) (_ : is_beta b) (_ : P0 b), P (alpha1 b))
         (_ : P0 beta0)
         (_ : forall (g : gamma) (_ : is_gamma g) (_ : P1 g), P0 (beta1 g))
         (_ : P1 gamma0)
         (_ : forall (a : alpha) (_ : is_alpha a) 
                (_ : P a) (b : beta) (_ : is_beta b) 
                (_ : P0 b),
              P1 (gamma1 a b))
         (s1 : gamma) (_ : is_gamma s1),
       P1 s1 :=
  fun (P : forall _ : alpha, Type) (P0 : forall _ : beta, Type)
    (P1 : forall _ : gamma, Type) (His_alpha0 : P alpha0)
    (His_alpha1 : forall (b : beta) (_ : is_beta b) (_ : P0 b), P (alpha1 b))
    (His_beta0 : P0 beta0)
    (His_beta1 : forall (g : gamma) (_ : is_gamma g) (_ : P1 g), P0 (beta1 g))
    (His_gamma0 : P1 gamma0)
    (His_gamma1 : forall (a : alpha) (_ : is_alpha a) 
                    (_ : P a) (b : beta) (_ : is_beta b) 
                    (_ : P0 b),
                  P1 (gamma1 a b)) =>
  fix is_alpha_induction_rec (s1 : alpha) (H : is_alpha s1) {struct H} :
      P s1 :=
    match H in is_alpha s2 return P s2 with
    | is_alpha0 => His_alpha0
    | is_alpha1 b Pb => His_alpha1 b Pb (is_beta_induction_rec b Pb)
    end
  with is_beta_induction_rec (s1 : beta) (H : is_beta s1) {struct H} : P0 s1 :=
    match H in is_beta s2 return P0 s2 with
    | is_beta0 => His_beta0
    | is_beta1 g Pg => His_beta1 g Pg (is_gamma_induction_rec g Pg)
    end
  with is_gamma_induction_rec (s1 : gamma) (H : is_gamma s1) {struct H} :
      P1 s1 :=
    match H in is_gamma s2 return P1 s2 with
    | is_gamma0 => His_gamma0
    | is_gamma1 a Pa b Pb =>
        His_gamma1 a Pa (is_alpha_induction_rec a Pa) b Pb
          (is_beta_induction_rec b Pb)
    end
  for
  is_gamma_induction_rec.
  Definition alpha_eqb_correct : forall x : alpha, @eqb_correct_on alpha alpha_eqb x :=
  fun x : alpha =>
  let common :
    forall (a1 : alpha)
      (_ : @eqb_fields_correct_on alpha alpha_tag alpha_fields_t alpha_fields
             alpha_construct (alpha_eqb_fields alpha_eqb) a1)
      (a2 : alpha)
      (_ : Datatypes.is_true
             (@eqb_body alpha alpha_tag alpha_fields_t alpha_fields_t
                alpha_fields (alpha_eqb_fields alpha_eqb) 
                (alpha_tag a1) (alpha_fields a1) a2)),
    @eq alpha a1 a2 :=
    @eqb_body_correct alpha alpha_tag alpha_fields_t alpha_fields
      alpha_construct alpha_constructP (alpha_eqb_fields alpha_eqb)
    in
  let common0 :
    forall (a1 : beta)
      (_ : @eqb_fields_correct_on beta beta_tag beta_fields_t beta_fields
             beta_construct (beta_eqb_fields beta_eqb) a1)
      (a2 : beta)
      (_ : Datatypes.is_true
             (@eqb_body beta beta_tag beta_fields_t beta_fields_t beta_fields
                (beta_eqb_fields beta_eqb) (beta_tag a1) 
                (beta_fields a1) a2)),
    @eq beta a1 a2 :=
    @eqb_body_correct beta beta_tag beta_fields_t beta_fields beta_construct
      beta_constructP (beta_eqb_fields beta_eqb)
    in
  let common1 :
    forall (a1 : gamma)
      (_ : @eqb_fields_correct_on gamma gamma_tag gamma_fields_t gamma_fields
             gamma_construct (gamma_eqb_fields gamma_eqb) a1)
      (a2 : gamma)
      (_ : Datatypes.is_true
             (@eqb_body gamma gamma_tag gamma_fields_t gamma_fields_t
                gamma_fields (gamma_eqb_fields gamma_eqb) 
                (gamma_tag a1) (gamma_fields a1) a2)),
    @eq gamma a1 a2 :=
    @eqb_body_correct gamma gamma_tag gamma_fields_t gamma_fields
      gamma_construct gamma_constructP (gamma_eqb_fields gamma_eqb)
    in
  alpha_induction (@eqb_correct_on alpha alpha_eqb)
    (@eqb_correct_on beta beta_eqb) (@eqb_correct_on gamma gamma_eqb)
    (common alpha0
       (fun x0 : alpha_fields_t (alpha_tag alpha0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (alpha_eqb_fields alpha_eqb (alpha_tag alpha0)
                        (alpha_fields alpha0) i)
                     true,
             @eq (option alpha) (@Some alpha alpha0)
               (alpha_construct (alpha_tag alpha0) i))
        with
        | Box_alpha_alpha0 =>
            @impliesP bnil
              (@eq (option alpha) (@Some alpha alpha0)
                 (alpha_construct (alpha_tag alpha0) Box_alpha_alpha0))
              (@eq_ind_r_nP tnil
                 (@eq (option alpha) (@Some alpha alpha0)
                    (alpha_construct (alpha_tag alpha0) Box_alpha_alpha0))
                 (@eq_refl (option alpha) (@Some alpha alpha0)))
        end)
     :
     @eqb_correct_on alpha alpha_eqb alpha0)
    (fun (x0 : beta) (_ : is_beta x0) (h : @eqb_correct_on beta beta_eqb x0) =>
     common (alpha1 x0)
       (fun x1 : alpha_fields_t (alpha_tag (alpha1 x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (alpha_eqb_fields alpha_eqb (alpha_tag (alpha1 x0))
                        (alpha_fields (alpha1 x0)) i)
                     true,
             @eq (option alpha) (@Some alpha (alpha1 x0))
               (alpha_construct (alpha_tag (alpha1 x0)) i))
        with
        | Box_alpha_alpha1 Box_alpha_alpha1_0 =>
            @impliesP (bcons (beta_eqb x0 Box_alpha_alpha1_0) bnil)
              (@eq (option alpha) (@Some alpha (alpha1 x0))
                 (alpha_construct (alpha_tag (alpha1 x0))
                    (Box_alpha_alpha1 Box_alpha_alpha1_0)))
              (fun h0 : @eq bool (beta_eqb x0 Box_alpha_alpha1_0) true =>
               @eq_ind_r_nP (tcons beta tnil)
                 (fun w : beta =>
                  @eq (option alpha) (@Some alpha (alpha1 x0))
                    (alpha_construct (alpha_tag (alpha1 x0))
                       (Box_alpha_alpha1 w)))
                 x0 Box_alpha_alpha1_0 (h Box_alpha_alpha1_0 h0)
                 (@eq_refl (option alpha) (@Some alpha (alpha1 x0))))
        end)
     :
     @eqb_correct_on alpha alpha_eqb (alpha1 x0))
    (common0 beta0
       (fun x0 : beta_fields_t (beta_tag beta0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (beta_eqb_fields beta_eqb (beta_tag beta0)
                        (beta_fields beta0) i)
                     true,
             @eq (option beta) (@Some beta beta0)
               (beta_construct (beta_tag beta0) i))
        with
        | Box_beta_beta0 =>
            @impliesP bnil
              (@eq (option beta) (@Some beta beta0)
                 (beta_construct (beta_tag beta0) Box_beta_beta0))
              (@eq_ind_r_nP tnil
                 (@eq (option beta) (@Some beta beta0)
                    (beta_construct (beta_tag beta0) Box_beta_beta0))
                 (@eq_refl (option beta) (@Some beta beta0)))
        end)
     :
     @eqb_correct_on beta beta_eqb beta0)
    (fun (x0 : gamma) (_ : is_gamma x0)
       (h : @eqb_correct_on gamma gamma_eqb x0) =>
     common0 (beta1 x0)
       (fun x1 : beta_fields_t (beta_tag (beta1 x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (beta_eqb_fields beta_eqb (beta_tag (beta1 x0))
                        (beta_fields (beta1 x0)) i)
                     true,
             @eq (option beta) (@Some beta (beta1 x0))
               (beta_construct (beta_tag (beta1 x0)) i))
        with
        | Box_beta_beta1 Box_beta_beta1_0 =>
            @impliesP (bcons (gamma_eqb x0 Box_beta_beta1_0) bnil)
              (@eq (option beta) (@Some beta (beta1 x0))
                 (beta_construct (beta_tag (beta1 x0))
                    (Box_beta_beta1 Box_beta_beta1_0)))
              (fun h0 : @eq bool (gamma_eqb x0 Box_beta_beta1_0) true =>
               @eq_ind_r_nP (tcons gamma tnil)
                 (fun w : gamma =>
                  @eq (option beta) (@Some beta (beta1 x0))
                    (beta_construct (beta_tag (beta1 x0)) (Box_beta_beta1 w)))
                 x0 Box_beta_beta1_0 (h Box_beta_beta1_0 h0)
                 (@eq_refl (option beta) (@Some beta (beta1 x0))))
        end)
     :
     @eqb_correct_on beta beta_eqb (beta1 x0))
    (common1 gamma0
       (fun x0 : gamma_fields_t (gamma_tag gamma0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (gamma_eqb_fields gamma_eqb (gamma_tag gamma0)
                        (gamma_fields gamma0) i)
                     true,
             @eq (option gamma) (@Some gamma gamma0)
               (gamma_construct (gamma_tag gamma0) i))
        with
        | Box_gamma_gamma0 =>
            @impliesP bnil
              (@eq (option gamma) (@Some gamma gamma0)
                 (gamma_construct (gamma_tag gamma0) Box_gamma_gamma0))
              (@eq_ind_r_nP tnil
                 (@eq (option gamma) (@Some gamma gamma0)
                    (gamma_construct (gamma_tag gamma0) Box_gamma_gamma0))
                 (@eq_refl (option gamma) (@Some gamma gamma0)))
        end)
     :
     @eqb_correct_on gamma gamma_eqb gamma0)
    (fun (x0 : alpha) (_ : is_alpha x0)
       (h : @eqb_correct_on alpha alpha_eqb x0) (x1 : beta) 
       (_ : is_beta x1) (h0 : @eqb_correct_on beta beta_eqb x1) =>
     common1 (gamma1 x0 x1)
       (fun x2 : gamma_fields_t (gamma_tag (gamma1 x0 x1)) =>
        match
          x2 as i
          return
            (forall
               _ : @eq bool
                     (gamma_eqb_fields gamma_eqb (gamma_tag (gamma1 x0 x1))
                        (gamma_fields (gamma1 x0 x1)) i)
                     true,
             @eq (option gamma) (@Some gamma (gamma1 x0 x1))
               (gamma_construct (gamma_tag (gamma1 x0 x1)) i))
        with
        | Box_gamma_gamma1 Box_gamma_gamma1_0 Box_gamma_gamma1_1 =>
            @impliesP
              (bcons (alpha_eqb x0 Box_gamma_gamma1_0)
                 (bcons (beta_eqb x1 Box_gamma_gamma1_1) bnil))
              (@eq (option gamma) (@Some gamma (gamma1 x0 x1))
                 (gamma_construct (gamma_tag (gamma1 x0 x1))
                    (Box_gamma_gamma1 Box_gamma_gamma1_0 Box_gamma_gamma1_1)))
              (fun (h1 : @eq bool (alpha_eqb x0 Box_gamma_gamma1_0) true)
                 (h2 : @eq bool (beta_eqb x1 Box_gamma_gamma1_1) true) =>
               @eq_ind_r_nP (tcons alpha (tcons beta tnil))
                 (fun (w : alpha) (w0 : beta) =>
                  @eq (option gamma) (@Some gamma (gamma1 x0 x1))
                    (gamma_construct (gamma_tag (gamma1 x0 x1))
                       (Box_gamma_gamma1 w w0)))
                 x0 Box_gamma_gamma1_0 (h Box_gamma_gamma1_0 h1) x1
                 Box_gamma_gamma1_1 (h0 Box_gamma_gamma1_1 h2)
                 (@eq_refl (option gamma) (@Some gamma (gamma1 x0 x1))))
        end)
     :
     @eqb_correct_on gamma gamma_eqb (gamma1 x0 x1))
    x (is_alpha_inhab x).
  Definition beta_eqb_correct : forall x : beta, @eqb_correct_on beta beta_eqb x :=
  fun x : beta =>
  let common :
    forall (a1 : alpha)
      (_ : @eqb_fields_correct_on alpha alpha_tag alpha_fields_t alpha_fields
             alpha_construct (alpha_eqb_fields alpha_eqb) a1)
      (a2 : alpha)
      (_ : Datatypes.is_true
             (@eqb_body alpha alpha_tag alpha_fields_t alpha_fields_t
                alpha_fields (alpha_eqb_fields alpha_eqb) 
                (alpha_tag a1) (alpha_fields a1) a2)),
    @eq alpha a1 a2 :=
    @eqb_body_correct alpha alpha_tag alpha_fields_t alpha_fields
      alpha_construct alpha_constructP (alpha_eqb_fields alpha_eqb)
    in
  let common0 :
    forall (a1 : beta)
      (_ : @eqb_fields_correct_on beta beta_tag beta_fields_t beta_fields
             beta_construct (beta_eqb_fields beta_eqb) a1)
      (a2 : beta)
      (_ : Datatypes.is_true
             (@eqb_body beta beta_tag beta_fields_t beta_fields_t beta_fields
                (beta_eqb_fields beta_eqb) (beta_tag a1) 
                (beta_fields a1) a2)),
    @eq beta a1 a2 :=
    @eqb_body_correct beta beta_tag beta_fields_t beta_fields beta_construct
      beta_constructP (beta_eqb_fields beta_eqb)
    in
  let common1 :
    forall (a1 : gamma)
      (_ : @eqb_fields_correct_on gamma gamma_tag gamma_fields_t gamma_fields
             gamma_construct (gamma_eqb_fields gamma_eqb) a1)
      (a2 : gamma)
      (_ : Datatypes.is_true
             (@eqb_body gamma gamma_tag gamma_fields_t gamma_fields_t
                gamma_fields (gamma_eqb_fields gamma_eqb) 
                (gamma_tag a1) (gamma_fields a1) a2)),
    @eq gamma a1 a2 :=
    @eqb_body_correct gamma gamma_tag gamma_fields_t gamma_fields
      gamma_construct gamma_constructP (gamma_eqb_fields gamma_eqb)
    in
  beta_induction (@eqb_correct_on alpha alpha_eqb)
    (@eqb_correct_on beta beta_eqb) (@eqb_correct_on gamma gamma_eqb)
    (common alpha0
       (fun x0 : alpha_fields_t (alpha_tag alpha0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (alpha_eqb_fields alpha_eqb (alpha_tag alpha0)
                        (alpha_fields alpha0) i)
                     true,
             @eq (option alpha) (@Some alpha alpha0)
               (alpha_construct (alpha_tag alpha0) i))
        with
        | Box_alpha_alpha0 =>
            @impliesP bnil
              (@eq (option alpha) (@Some alpha alpha0)
                 (alpha_construct (alpha_tag alpha0) Box_alpha_alpha0))
              (@eq_ind_r_nP tnil
                 (@eq (option alpha) (@Some alpha alpha0)
                    (alpha_construct (alpha_tag alpha0) Box_alpha_alpha0))
                 (@eq_refl (option alpha) (@Some alpha alpha0)))
        end)
     :
     @eqb_correct_on alpha alpha_eqb alpha0)
    (fun (x0 : beta) (_ : is_beta x0) (h : @eqb_correct_on beta beta_eqb x0) =>
     common (alpha1 x0)
       (fun x1 : alpha_fields_t (alpha_tag (alpha1 x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (alpha_eqb_fields alpha_eqb (alpha_tag (alpha1 x0))
                        (alpha_fields (alpha1 x0)) i)
                     true,
             @eq (option alpha) (@Some alpha (alpha1 x0))
               (alpha_construct (alpha_tag (alpha1 x0)) i))
        with
        | Box_alpha_alpha1 Box_alpha_alpha1_0 =>
            @impliesP (bcons (beta_eqb x0 Box_alpha_alpha1_0) bnil)
              (@eq (option alpha) (@Some alpha (alpha1 x0))
                 (alpha_construct (alpha_tag (alpha1 x0))
                    (Box_alpha_alpha1 Box_alpha_alpha1_0)))
              (fun h0 : @eq bool (beta_eqb x0 Box_alpha_alpha1_0) true =>
               @eq_ind_r_nP (tcons beta tnil)
                 (fun w : beta =>
                  @eq (option alpha) (@Some alpha (alpha1 x0))
                    (alpha_construct (alpha_tag (alpha1 x0))
                       (Box_alpha_alpha1 w)))
                 x0 Box_alpha_alpha1_0 (h Box_alpha_alpha1_0 h0)
                 (@eq_refl (option alpha) (@Some alpha (alpha1 x0))))
        end)
     :
     @eqb_correct_on alpha alpha_eqb (alpha1 x0))
    (common0 beta0
       (fun x0 : beta_fields_t (beta_tag beta0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (beta_eqb_fields beta_eqb (beta_tag beta0)
                        (beta_fields beta0) i)
                     true,
             @eq (option beta) (@Some beta beta0)
               (beta_construct (beta_tag beta0) i))
        with
        | Box_beta_beta0 =>
            @impliesP bnil
              (@eq (option beta) (@Some beta beta0)
                 (beta_construct (beta_tag beta0) Box_beta_beta0))
              (@eq_ind_r_nP tnil
                 (@eq (option beta) (@Some beta beta0)
                    (beta_construct (beta_tag beta0) Box_beta_beta0))
                 (@eq_refl (option beta) (@Some beta beta0)))
        end)
     :
     @eqb_correct_on beta beta_eqb beta0)
    (fun (x0 : gamma) (_ : is_gamma x0)
       (h : @eqb_correct_on gamma gamma_eqb x0) =>
     common0 (beta1 x0)
       (fun x1 : beta_fields_t (beta_tag (beta1 x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (beta_eqb_fields beta_eqb (beta_tag (beta1 x0))
                        (beta_fields (beta1 x0)) i)
                     true,
             @eq (option beta) (@Some beta (beta1 x0))
               (beta_construct (beta_tag (beta1 x0)) i))
        with
        | Box_beta_beta1 Box_beta_beta1_0 =>
            @impliesP (bcons (gamma_eqb x0 Box_beta_beta1_0) bnil)
              (@eq (option beta) (@Some beta (beta1 x0))
                 (beta_construct (beta_tag (beta1 x0))
                    (Box_beta_beta1 Box_beta_beta1_0)))
              (fun h0 : @eq bool (gamma_eqb x0 Box_beta_beta1_0) true =>
               @eq_ind_r_nP (tcons gamma tnil)
                 (fun w : gamma =>
                  @eq (option beta) (@Some beta (beta1 x0))
                    (beta_construct (beta_tag (beta1 x0)) (Box_beta_beta1 w)))
                 x0 Box_beta_beta1_0 (h Box_beta_beta1_0 h0)
                 (@eq_refl (option beta) (@Some beta (beta1 x0))))
        end)
     :
     @eqb_correct_on beta beta_eqb (beta1 x0))
    (common1 gamma0
       (fun x0 : gamma_fields_t (gamma_tag gamma0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (gamma_eqb_fields gamma_eqb (gamma_tag gamma0)
                        (gamma_fields gamma0) i)
                     true,
             @eq (option gamma) (@Some gamma gamma0)
               (gamma_construct (gamma_tag gamma0) i))
        with
        | Box_gamma_gamma0 =>
            @impliesP bnil
              (@eq (option gamma) (@Some gamma gamma0)
                 (gamma_construct (gamma_tag gamma0) Box_gamma_gamma0))
              (@eq_ind_r_nP tnil
                 (@eq (option gamma) (@Some gamma gamma0)
                    (gamma_construct (gamma_tag gamma0) Box_gamma_gamma0))
                 (@eq_refl (option gamma) (@Some gamma gamma0)))
        end)
     :
     @eqb_correct_on gamma gamma_eqb gamma0)
    (fun (x0 : alpha) (_ : is_alpha x0)
       (h : @eqb_correct_on alpha alpha_eqb x0) (x1 : beta) 
       (_ : is_beta x1) (h0 : @eqb_correct_on beta beta_eqb x1) =>
     common1 (gamma1 x0 x1)
       (fun x2 : gamma_fields_t (gamma_tag (gamma1 x0 x1)) =>
        match
          x2 as i
          return
            (forall
               _ : @eq bool
                     (gamma_eqb_fields gamma_eqb (gamma_tag (gamma1 x0 x1))
                        (gamma_fields (gamma1 x0 x1)) i)
                     true,
             @eq (option gamma) (@Some gamma (gamma1 x0 x1))
               (gamma_construct (gamma_tag (gamma1 x0 x1)) i))
        with
        | Box_gamma_gamma1 Box_gamma_gamma1_0 Box_gamma_gamma1_1 =>
            @impliesP
              (bcons (alpha_eqb x0 Box_gamma_gamma1_0)
                 (bcons (beta_eqb x1 Box_gamma_gamma1_1) bnil))
              (@eq (option gamma) (@Some gamma (gamma1 x0 x1))
                 (gamma_construct (gamma_tag (gamma1 x0 x1))
                    (Box_gamma_gamma1 Box_gamma_gamma1_0 Box_gamma_gamma1_1)))
              (fun (h1 : @eq bool (alpha_eqb x0 Box_gamma_gamma1_0) true)
                 (h2 : @eq bool (beta_eqb x1 Box_gamma_gamma1_1) true) =>
               @eq_ind_r_nP (tcons alpha (tcons beta tnil))
                 (fun (w : alpha) (w0 : beta) =>
                  @eq (option gamma) (@Some gamma (gamma1 x0 x1))
                    (gamma_construct (gamma_tag (gamma1 x0 x1))
                       (Box_gamma_gamma1 w w0)))
                 x0 Box_gamma_gamma1_0 (h Box_gamma_gamma1_0 h1) x1
                 Box_gamma_gamma1_1 (h0 Box_gamma_gamma1_1 h2)
                 (@eq_refl (option gamma) (@Some gamma (gamma1 x0 x1))))
        end)
     :
     @eqb_correct_on gamma gamma_eqb (gamma1 x0 x1))
    x (is_beta_inhab x).
  Definition gamma_eqb_correct : forall x : gamma, @eqb_correct_on gamma gamma_eqb x :=
  fun x : gamma =>
  let common :
    forall (a1 : alpha)
      (_ : @eqb_fields_correct_on alpha alpha_tag alpha_fields_t alpha_fields
             alpha_construct (alpha_eqb_fields alpha_eqb) a1)
      (a2 : alpha)
      (_ : Datatypes.is_true
             (@eqb_body alpha alpha_tag alpha_fields_t alpha_fields_t
                alpha_fields (alpha_eqb_fields alpha_eqb) 
                (alpha_tag a1) (alpha_fields a1) a2)),
    @eq alpha a1 a2 :=
    @eqb_body_correct alpha alpha_tag alpha_fields_t alpha_fields
      alpha_construct alpha_constructP (alpha_eqb_fields alpha_eqb)
    in
  let common0 :
    forall (a1 : beta)
      (_ : @eqb_fields_correct_on beta beta_tag beta_fields_t beta_fields
             beta_construct (beta_eqb_fields beta_eqb) a1)
      (a2 : beta)
      (_ : Datatypes.is_true
             (@eqb_body beta beta_tag beta_fields_t beta_fields_t beta_fields
                (beta_eqb_fields beta_eqb) (beta_tag a1) 
                (beta_fields a1) a2)),
    @eq beta a1 a2 :=
    @eqb_body_correct beta beta_tag beta_fields_t beta_fields beta_construct
      beta_constructP (beta_eqb_fields beta_eqb)
    in
  let common1 :
    forall (a1 : gamma)
      (_ : @eqb_fields_correct_on gamma gamma_tag gamma_fields_t gamma_fields
             gamma_construct (gamma_eqb_fields gamma_eqb) a1)
      (a2 : gamma)
      (_ : Datatypes.is_true
             (@eqb_body gamma gamma_tag gamma_fields_t gamma_fields_t
                gamma_fields (gamma_eqb_fields gamma_eqb) 
                (gamma_tag a1) (gamma_fields a1) a2)),
    @eq gamma a1 a2 :=
    @eqb_body_correct gamma gamma_tag gamma_fields_t gamma_fields
      gamma_construct gamma_constructP (gamma_eqb_fields gamma_eqb)
    in
  gamma_induction (@eqb_correct_on alpha alpha_eqb)
    (@eqb_correct_on beta beta_eqb) (@eqb_correct_on gamma gamma_eqb)
    (common alpha0
       (fun x0 : alpha_fields_t (alpha_tag alpha0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (alpha_eqb_fields alpha_eqb (alpha_tag alpha0)
                        (alpha_fields alpha0) i)
                     true,
             @eq (option alpha) (@Some alpha alpha0)
               (alpha_construct (alpha_tag alpha0) i))
        with
        | Box_alpha_alpha0 =>
            @impliesP bnil
              (@eq (option alpha) (@Some alpha alpha0)
                 (alpha_construct (alpha_tag alpha0) Box_alpha_alpha0))
              (@eq_ind_r_nP tnil
                 (@eq (option alpha) (@Some alpha alpha0)
                    (alpha_construct (alpha_tag alpha0) Box_alpha_alpha0))
                 (@eq_refl (option alpha) (@Some alpha alpha0)))
        end)
     :
     @eqb_correct_on alpha alpha_eqb alpha0)
    (fun (x0 : beta) (_ : is_beta x0) (h : @eqb_correct_on beta beta_eqb x0) =>
     common (alpha1 x0)
       (fun x1 : alpha_fields_t (alpha_tag (alpha1 x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (alpha_eqb_fields alpha_eqb (alpha_tag (alpha1 x0))
                        (alpha_fields (alpha1 x0)) i)
                     true,
             @eq (option alpha) (@Some alpha (alpha1 x0))
               (alpha_construct (alpha_tag (alpha1 x0)) i))
        with
        | Box_alpha_alpha1 Box_alpha_alpha1_0 =>
            @impliesP (bcons (beta_eqb x0 Box_alpha_alpha1_0) bnil)
              (@eq (option alpha) (@Some alpha (alpha1 x0))
                 (alpha_construct (alpha_tag (alpha1 x0))
                    (Box_alpha_alpha1 Box_alpha_alpha1_0)))
              (fun h0 : @eq bool (beta_eqb x0 Box_alpha_alpha1_0) true =>
               @eq_ind_r_nP (tcons beta tnil)
                 (fun w : beta =>
                  @eq (option alpha) (@Some alpha (alpha1 x0))
                    (alpha_construct (alpha_tag (alpha1 x0))
                       (Box_alpha_alpha1 w)))
                 x0 Box_alpha_alpha1_0 (h Box_alpha_alpha1_0 h0)
                 (@eq_refl (option alpha) (@Some alpha (alpha1 x0))))
        end)
     :
     @eqb_correct_on alpha alpha_eqb (alpha1 x0))
    (common0 beta0
       (fun x0 : beta_fields_t (beta_tag beta0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (beta_eqb_fields beta_eqb (beta_tag beta0)
                        (beta_fields beta0) i)
                     true,
             @eq (option beta) (@Some beta beta0)
               (beta_construct (beta_tag beta0) i))
        with
        | Box_beta_beta0 =>
            @impliesP bnil
              (@eq (option beta) (@Some beta beta0)
                 (beta_construct (beta_tag beta0) Box_beta_beta0))
              (@eq_ind_r_nP tnil
                 (@eq (option beta) (@Some beta beta0)
                    (beta_construct (beta_tag beta0) Box_beta_beta0))
                 (@eq_refl (option beta) (@Some beta beta0)))
        end)
     :
     @eqb_correct_on beta beta_eqb beta0)
    (fun (x0 : gamma) (_ : is_gamma x0)
       (h : @eqb_correct_on gamma gamma_eqb x0) =>
     common0 (beta1 x0)
       (fun x1 : beta_fields_t (beta_tag (beta1 x0)) =>
        match
          x1 as i
          return
            (forall
               _ : @eq bool
                     (beta_eqb_fields beta_eqb (beta_tag (beta1 x0))
                        (beta_fields (beta1 x0)) i)
                     true,
             @eq (option beta) (@Some beta (beta1 x0))
               (beta_construct (beta_tag (beta1 x0)) i))
        with
        | Box_beta_beta1 Box_beta_beta1_0 =>
            @impliesP (bcons (gamma_eqb x0 Box_beta_beta1_0) bnil)
              (@eq (option beta) (@Some beta (beta1 x0))
                 (beta_construct (beta_tag (beta1 x0))
                    (Box_beta_beta1 Box_beta_beta1_0)))
              (fun h0 : @eq bool (gamma_eqb x0 Box_beta_beta1_0) true =>
               @eq_ind_r_nP (tcons gamma tnil)
                 (fun w : gamma =>
                  @eq (option beta) (@Some beta (beta1 x0))
                    (beta_construct (beta_tag (beta1 x0)) (Box_beta_beta1 w)))
                 x0 Box_beta_beta1_0 (h Box_beta_beta1_0 h0)
                 (@eq_refl (option beta) (@Some beta (beta1 x0))))
        end)
     :
     @eqb_correct_on beta beta_eqb (beta1 x0))
    (common1 gamma0
       (fun x0 : gamma_fields_t (gamma_tag gamma0) =>
        match
          x0 as i
          return
            (forall
               _ : @eq bool
                     (gamma_eqb_fields gamma_eqb (gamma_tag gamma0)
                        (gamma_fields gamma0) i)
                     true,
             @eq (option gamma) (@Some gamma gamma0)
               (gamma_construct (gamma_tag gamma0) i))
        with
        | Box_gamma_gamma0 =>
            @impliesP bnil
              (@eq (option gamma) (@Some gamma gamma0)
                 (gamma_construct (gamma_tag gamma0) Box_gamma_gamma0))
              (@eq_ind_r_nP tnil
                 (@eq (option gamma) (@Some gamma gamma0)
                    (gamma_construct (gamma_tag gamma0) Box_gamma_gamma0))
                 (@eq_refl (option gamma) (@Some gamma gamma0)))
        end)
     :
     @eqb_correct_on gamma gamma_eqb gamma0)
    (fun (x0 : alpha) (_ : is_alpha x0)
       (h : @eqb_correct_on alpha alpha_eqb x0) (x1 : beta) 
       (_ : is_beta x1) (h0 : @eqb_correct_on beta beta_eqb x1) =>
     common1 (gamma1 x0 x1)
       (fun x2 : gamma_fields_t (gamma_tag (gamma1 x0 x1)) =>
        match
          x2 as i
          return
            (forall
               _ : @eq bool
                     (gamma_eqb_fields gamma_eqb (gamma_tag (gamma1 x0 x1))
                        (gamma_fields (gamma1 x0 x1)) i)
                     true,
             @eq (option gamma) (@Some gamma (gamma1 x0 x1))
               (gamma_construct (gamma_tag (gamma1 x0 x1)) i))
        with
        | Box_gamma_gamma1 Box_gamma_gamma1_0 Box_gamma_gamma1_1 =>
            @impliesP
              (bcons (alpha_eqb x0 Box_gamma_gamma1_0)
                 (bcons (beta_eqb x1 Box_gamma_gamma1_1) bnil))
              (@eq (option gamma) (@Some gamma (gamma1 x0 x1))
                 (gamma_construct (gamma_tag (gamma1 x0 x1))
                    (Box_gamma_gamma1 Box_gamma_gamma1_0 Box_gamma_gamma1_1)))
              (fun (h1 : @eq bool (alpha_eqb x0 Box_gamma_gamma1_0) true)
                 (h2 : @eq bool (beta_eqb x1 Box_gamma_gamma1_1) true) =>
               @eq_ind_r_nP (tcons alpha (tcons beta tnil))
                 (fun (w : alpha) (w0 : beta) =>
                  @eq (option gamma) (@Some gamma (gamma1 x0 x1))
                    (gamma_construct (gamma_tag (gamma1 x0 x1))
                       (Box_gamma_gamma1 w w0)))
                 x0 Box_gamma_gamma1_0 (h Box_gamma_gamma1_0 h1) x1
                 Box_gamma_gamma1_1 (h0 Box_gamma_gamma1_1 h2)
                 (@eq_refl (option gamma) (@Some gamma (gamma1 x0 x1))))
        end)
     :
     @eqb_correct_on gamma gamma_eqb (gamma1 x0 x1))
    x (is_gamma_inhab x).
  Definition alpha_eqb_refl : forall x : alpha, @eqb_refl_on alpha alpha_eqb x :=
  fun x : alpha =>
  let common :
    forall (a : alpha)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on alpha alpha_tag alpha_fields_t alpha_fields
                (alpha_eqb_fields alpha_eqb) a)),
    Datatypes.is_true
      (@eqb_body alpha alpha_tag alpha_fields_t alpha_fields_t alpha_fields
         (alpha_eqb_fields alpha_eqb) (alpha_tag a) 
         (alpha_fields a) a) :=
    @eqb_body_refl alpha alpha_tag alpha_fields_t alpha_fields alpha_construct
      alpha_constructP (alpha_eqb_fields alpha_eqb)
    in
  let common0 :
    forall (a : beta)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on beta beta_tag beta_fields_t beta_fields
                (beta_eqb_fields beta_eqb) a)),
    Datatypes.is_true
      (@eqb_body beta beta_tag beta_fields_t beta_fields_t beta_fields
         (beta_eqb_fields beta_eqb) (beta_tag a) (beta_fields a) a) :=
    @eqb_body_refl beta beta_tag beta_fields_t beta_fields beta_construct
      beta_constructP (beta_eqb_fields beta_eqb)
    in
  let common1 :
    forall (a : gamma)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on gamma gamma_tag gamma_fields_t gamma_fields
                (gamma_eqb_fields gamma_eqb) a)),
    Datatypes.is_true
      (@eqb_body gamma gamma_tag gamma_fields_t gamma_fields_t gamma_fields
         (gamma_eqb_fields gamma_eqb) (gamma_tag a) 
         (gamma_fields a) a) :=
    @eqb_body_refl gamma gamma_tag gamma_fields_t gamma_fields gamma_construct
      gamma_constructP (gamma_eqb_fields gamma_eqb)
    in
  alpha_induction (@eqb_refl_on alpha alpha_eqb) (@eqb_refl_on beta beta_eqb)
    (@eqb_refl_on gamma gamma_eqb)
    (common alpha0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on alpha alpha_eqb alpha0)
    (fun (x0 : beta) (_ : is_beta x0) (h : @eqb_refl_on beta beta_eqb x0) =>
     common (alpha1 x0) (eqb_refl_statementP (bcons (beta_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on alpha alpha_eqb (alpha1 x0))
    (common0 beta0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on beta beta_eqb beta0)
    (fun (x0 : gamma) (_ : is_gamma x0) (h : @eqb_refl_on gamma gamma_eqb x0) =>
     common0 (beta1 x0) (eqb_refl_statementP (bcons (gamma_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on beta beta_eqb (beta1 x0))
    (common1 gamma0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on gamma gamma_eqb gamma0)
    (fun (x0 : alpha) (_ : is_alpha x0) (h : @eqb_refl_on alpha alpha_eqb x0)
       (x1 : beta) (_ : is_beta x1) (h0 : @eqb_refl_on beta beta_eqb x1) =>
     common1 (gamma1 x0 x1)
       (eqb_refl_statementP
          (bcons (beta_eqb x1 x1) (bcons (alpha_eqb x0 x0) bnil)) h0 h)
     :
     @eqb_refl_on gamma gamma_eqb (gamma1 x0 x1))
    x (is_alpha_inhab x).
  Definition beta_eqb_refl : forall x : beta, @eqb_refl_on beta beta_eqb x :=
  fun x : beta =>
  let common :
    forall (a : alpha)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on alpha alpha_tag alpha_fields_t alpha_fields
                (alpha_eqb_fields alpha_eqb) a)),
    Datatypes.is_true
      (@eqb_body alpha alpha_tag alpha_fields_t alpha_fields_t alpha_fields
         (alpha_eqb_fields alpha_eqb) (alpha_tag a) 
         (alpha_fields a) a) :=
    @eqb_body_refl alpha alpha_tag alpha_fields_t alpha_fields alpha_construct
      alpha_constructP (alpha_eqb_fields alpha_eqb)
    in
  let common0 :
    forall (a : beta)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on beta beta_tag beta_fields_t beta_fields
                (beta_eqb_fields beta_eqb) a)),
    Datatypes.is_true
      (@eqb_body beta beta_tag beta_fields_t beta_fields_t beta_fields
         (beta_eqb_fields beta_eqb) (beta_tag a) (beta_fields a) a) :=
    @eqb_body_refl beta beta_tag beta_fields_t beta_fields beta_construct
      beta_constructP (beta_eqb_fields beta_eqb)
    in
  let common1 :
    forall (a : gamma)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on gamma gamma_tag gamma_fields_t gamma_fields
                (gamma_eqb_fields gamma_eqb) a)),
    Datatypes.is_true
      (@eqb_body gamma gamma_tag gamma_fields_t gamma_fields_t gamma_fields
         (gamma_eqb_fields gamma_eqb) (gamma_tag a) 
         (gamma_fields a) a) :=
    @eqb_body_refl gamma gamma_tag gamma_fields_t gamma_fields gamma_construct
      gamma_constructP (gamma_eqb_fields gamma_eqb)
    in
  beta_induction (@eqb_refl_on alpha alpha_eqb) (@eqb_refl_on beta beta_eqb)
    (@eqb_refl_on gamma gamma_eqb)
    (common alpha0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on alpha alpha_eqb alpha0)
    (fun (x0 : beta) (_ : is_beta x0) (h : @eqb_refl_on beta beta_eqb x0) =>
     common (alpha1 x0) (eqb_refl_statementP (bcons (beta_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on alpha alpha_eqb (alpha1 x0))
    (common0 beta0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on beta beta_eqb beta0)
    (fun (x0 : gamma) (_ : is_gamma x0) (h : @eqb_refl_on gamma gamma_eqb x0) =>
     common0 (beta1 x0) (eqb_refl_statementP (bcons (gamma_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on beta beta_eqb (beta1 x0))
    (common1 gamma0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on gamma gamma_eqb gamma0)
    (fun (x0 : alpha) (_ : is_alpha x0) (h : @eqb_refl_on alpha alpha_eqb x0)
       (x1 : beta) (_ : is_beta x1) (h0 : @eqb_refl_on beta beta_eqb x1) =>
     common1 (gamma1 x0 x1)
       (eqb_refl_statementP
          (bcons (beta_eqb x1 x1) (bcons (alpha_eqb x0 x0) bnil)) h0 h)
     :
     @eqb_refl_on gamma gamma_eqb (gamma1 x0 x1))
    x (is_beta_inhab x).
  Definition gamma_eqb_refl : forall x : gamma, @eqb_refl_on gamma gamma_eqb x :=
  fun x : gamma =>
  let common :
    forall (a : alpha)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on alpha alpha_tag alpha_fields_t alpha_fields
                (alpha_eqb_fields alpha_eqb) a)),
    Datatypes.is_true
      (@eqb_body alpha alpha_tag alpha_fields_t alpha_fields_t alpha_fields
         (alpha_eqb_fields alpha_eqb) (alpha_tag a) 
         (alpha_fields a) a) :=
    @eqb_body_refl alpha alpha_tag alpha_fields_t alpha_fields alpha_construct
      alpha_constructP (alpha_eqb_fields alpha_eqb)
    in
  let common0 :
    forall (a : beta)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on beta beta_tag beta_fields_t beta_fields
                (beta_eqb_fields beta_eqb) a)),
    Datatypes.is_true
      (@eqb_body beta beta_tag beta_fields_t beta_fields_t beta_fields
         (beta_eqb_fields beta_eqb) (beta_tag a) (beta_fields a) a) :=
    @eqb_body_refl beta beta_tag beta_fields_t beta_fields beta_construct
      beta_constructP (beta_eqb_fields beta_eqb)
    in
  let common1 :
    forall (a : gamma)
      (_ : Datatypes.is_true
             (@eqb_fields_refl_on gamma gamma_tag gamma_fields_t gamma_fields
                (gamma_eqb_fields gamma_eqb) a)),
    Datatypes.is_true
      (@eqb_body gamma gamma_tag gamma_fields_t gamma_fields_t gamma_fields
         (gamma_eqb_fields gamma_eqb) (gamma_tag a) 
         (gamma_fields a) a) :=
    @eqb_body_refl gamma gamma_tag gamma_fields_t gamma_fields gamma_construct
      gamma_constructP (gamma_eqb_fields gamma_eqb)
    in
  gamma_induction (@eqb_refl_on alpha alpha_eqb) (@eqb_refl_on beta beta_eqb)
    (@eqb_refl_on gamma gamma_eqb)
    (common alpha0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on alpha alpha_eqb alpha0)
    (fun (x0 : beta) (_ : is_beta x0) (h : @eqb_refl_on beta beta_eqb x0) =>
     common (alpha1 x0) (eqb_refl_statementP (bcons (beta_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on alpha alpha_eqb (alpha1 x0))
    (common0 beta0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on beta beta_eqb beta0)
    (fun (x0 : gamma) (_ : is_gamma x0) (h : @eqb_refl_on gamma gamma_eqb x0) =>
     common0 (beta1 x0) (eqb_refl_statementP (bcons (gamma_eqb x0 x0) bnil) h)
     :
     @eqb_refl_on beta beta_eqb (beta1 x0))
    (common1 gamma0 (eqb_refl_statementP bnil)
     :
     @eqb_refl_on gamma gamma_eqb gamma0)
    (fun (x0 : alpha) (_ : is_alpha x0) (h : @eqb_refl_on alpha alpha_eqb x0)
       (x1 : beta) (_ : is_beta x1) (h0 : @eqb_refl_on beta beta_eqb x1) =>
     common1 (gamma1 x0 x1)
       (eqb_refl_statementP
          (bcons (beta_eqb x1 x1) (bcons (alpha_eqb x0 x0) bnil)) h0 h)
     :
     @eqb_refl_on gamma gamma_eqb (gamma1 x0 x1))
    x (is_gamma_inhab x).
  Definition alpha_eqb_OK : forall x1 x2 : alpha, reflect (@eq alpha x1 x2) (alpha_eqb x1 x2) :=
  @iffP2 alpha alpha_eqb alpha_eqb_correct alpha_eqb_refl.
  Definition beta_eqb_OK : forall x1 x2 : beta, reflect (@eq beta x1 x2) (beta_eqb x1 x2) :=
  @iffP2 beta beta_eqb beta_eqb_correct beta_eqb_refl.
  Definition gamma_eqb_OK : forall x1 x2 : gamma, reflect (@eq gamma x1 x2) (gamma_eqb x1 x2) :=
  @iffP2 gamma gamma_eqb gamma_eqb_correct gamma_eqb_refl.
  Definition alpha_eqb_OK_sumbool : forall x y : alpha, sumbool (@eq alpha x y) (not (@eq alpha x y)) :=
  reflect_dec alpha alpha_eqb alpha_eqb_OK.
  Definition beta_eqb_OK_sumbool : forall x y : beta, sumbool (@eq beta x y) (not (@eq beta x y)) :=
  reflect_dec beta beta_eqb beta_eqb_OK.
  Definition gamma_eqb_OK_sumbool : forall x y : gamma, sumbool (@eq gamma x y) (not (@eq gamma x y)) :=
  reflect_dec gamma gamma_eqb gamma_eqb_OK.
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
