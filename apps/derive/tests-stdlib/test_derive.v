From elpi.apps Require Import derive.std derive.legacy derive.experimental.
From elpi.apps Require Import test_derive_corelib.

Elpi derive Coverage.empty.
Elpi derive Coverage.unit.
Elpi derive Coverage.peano.
Elpi derive Coverage.option.
Elpi derive Coverage.pair.
Elpi derive Coverage.seq.
Elpi derive Coverage.box_peano.
Elpi derive Coverage.rose.
Elpi derive Coverage.rose_p.
Elpi derive Coverage.rose_o.
Elpi derive Coverage.nest.
Elpi derive Coverage.w.
Elpi derive Coverage.vect.
Elpi derive Coverage.dyn.
Fail Elpi derive Coverage.zeta.
Elpi derive Coverage.beta.
Elpi derive Coverage.iota.
(* Elpi derive Coverage.large. search slow *)
Elpi derive Coverage.prim_int.
Elpi derive Coverage.fo_record.
Elpi derive Coverage.pa_record.
Elpi derive Coverage.pr_record.
Elpi derive Coverage.dep_record.
Elpi derive Coverage.enum.

(* ---------------------------------------------------- *)

Elpi derive bool.

#[verbose] Elpi derive nat.

Redirect "tmp" Check nat_eqb : nat -> nat -> bool.
Redirect "tmp" Check is_nat : nat -> Type.
Redirect "tmp" Check is_nat_inhab : forall x, is_nat x.
Redirect "tmp" Check is_nat_functor : forall x, is_nat x -> is_nat x.
Redirect "tmp" Check nat_induction : forall P, P 0 -> (forall n, P n -> P (S n)) -> forall x, is_nat x -> P x.

Redirect "tmp" Check nat_tag : nat -> Numbers.BinNums.positive.
Redirect "tmp" Check nat_fields_t : Numbers.BinNums.positive -> Type.
Redirect "tmp" Check nat_fields : forall (n:nat), nat_fields_t (nat_tag n).
Redirect "tmp" Check nat_construct : forall (p: Numbers.BinNums.positive),  nat_fields_t p -> option nat.
Redirect "tmp" Check nat_constructP : forall (n:nat), nat_construct (nat_tag n) (nat_fields n) = Some n.
Redirect "tmp" Check nat_eqb : nat -> nat -> bool.
Redirect "tmp" Check nat_eqb_correct.
Redirect "tmp" Check nat_eqb_refl.
(* ---------------------------------------------------- *)

Elpi derive.param1 andb.

(* Prelude: Elpi derive list. *)

Redirect "tmp" Check list_map : forall A B, (A -> B) -> list A -> list B.
Redirect "tmp" Check is_nil : forall A P, is_list A P (@nil A).
Redirect "tmp" Check is_cons : forall A P x (Px : P x) tl (Ptl : is_list A P tl), is_list A P (cons x tl).
Redirect "tmp" Check is_list_functor : forall A P Q, (forall x, P x -> Q x) -> forall l, is_list A P l -> is_list A Q l.
Redirect "tmp" Check list_induction : forall A PA P, P nil -> (forall x, PA x -> forall xs, P xs -> P (cons x xs)) -> forall l, is_list A PA l -> P l.
Redirect "tmp" Check list_tag : forall A, list A -> Numbers.BinNums.positive.
Redirect "tmp" Check list_fields_t : (Type -> Numbers.BinNums.positive -> Type).
Redirect "tmp" Check list_fields : forall (A:Type) (l:list A), list_fields_t A (list_tag A l).
Redirect "tmp" Check list_construct : forall (A:Type) (p: Numbers.BinNums.positive),  list_fields_t A p -> option (list A).
Redirect "tmp" Check list_constructP : forall (A:Type) (l:list A), list_construct A (list_tag A l) (list_fields A l) = Some l.
Redirect "tmp" Check list_eqb : forall A, (A -> A -> bool) -> list A -> list A -> bool.
Redirect "tmp" Check list_eqb_correct.
Redirect "tmp" Check list_eqb_refl.
(* ---------------------------------------------------- *)

Require Vector.
Elpi Print derive "elpi.apps.derive.tests/derive".
#[only(eqOK), verbose] derive nat.
Module Vector.
derive Vector.t.
End Vector.

Redirect "tmp" Check Vector.t_eq : forall A, (A -> A -> bool) -> forall n, Vector.t A n -> Vector.t A n -> bool.
Redirect "tmp" Check Vector.t_isk_nil : forall A n, Vector.t A n -> bool.
Redirect "tmp" Check Vector.t_isk_cons : forall A n, Vector.t A n -> bool.
Redirect "tmp" Check Vector.t_map : forall A B, (A -> B) -> forall n, Vector.t A n -> Vector.t B n.
Redirect "tmp" Check Vector.t_getk_cons1 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> A.
Redirect "tmp" Check Vector.t_getk_cons2 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> nat.
Redirect "tmp" Check Vector.t_getk_cons3 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> { k : nat & Vector.t A k}.
Redirect "tmp" Check Vector.is_t : forall A, (A -> Type) -> forall n, is_nat n -> Vector.t A n -> Type.
Redirect "tmp" Check Vector.is_nil : forall A (PA : A -> Type), Vector.is_t A PA 0 is_O (Vector.nil A).
Redirect "tmp" Check Vector.is_cons : forall A (PA : A -> Type) (a : A), PA a -> forall n (Pn : is_nat n) (H : Vector.t A n),
       Vector.is_t A PA n Pn H -> Vector.is_t A PA (S n) (is_S n Pn) (Vector.cons A a n H).
Redirect "tmp" Check Vector.is_t_functor : forall A PA QA (H : forall x, PA x -> QA x), forall n nR v, Vector.is_t A PA n nR v -> Vector.is_t A QA n nR v.
Redirect "tmp" Check Vector.t_induction : forall A PA (P : forall n, is_nat n -> Vector.t A n -> Type), P 0 is_O (Vector.nil A) -> (forall a, PA a -> forall m mR, forall (v : Vector.t A m), P m mR v -> P (S m) (is_S m mR) (Vector.cons A a m v)) -> forall n nR v, Vector.is_t A PA n nR v -> P n nR v.
Redirect "tmp" Check Vector.t_tag : forall A i, Vector.t A i -> Numbers.BinNums.positive.
Fail Check Vector.t_fields_t : (Type -> Numbers.BinNums.positive -> Type).
Fail Check Vector.t_fields : forall (A:Type) (n:nat) (l:Vector.t A n), Vector.t_fields_t A (Vector.t_tag A l).
Fail Check Vector.t_construct : forall (A:Type) (p: Numbers.BinNums.positive),  Vector.t_fields_t A p -> option (Vector.t A).
Fail Check Vector.t_constructP : forall (A:Type) (l:Vector.t A), Vector.t_construct A (Vector.t_tag A l) (Vector.t_fields A l) = Some l.
Fail Check Vector.t_eqb : forall A, (A -> A -> bool) -> forall n, Vector.t A n -> Vector.t A n -> bool.

(* ---------------------------------------------------- *)

Inductive W A := B (f : A -> W).

Elpi derive W.
(* Not implemented yet :-/ *)
Fail Check W_induction : forall A (P : W A -> Type),
       (forall f, (forall x, UnitPred A x -> P (f x)) -> P (B A f)) ->
       forall x, P x.
Redirect "tmp" Check W_tag : forall A, W A -> Numbers.BinNums.positive.
Fail Check W_fields_t : (Type -> Numbers.BinNums.positive -> Type).
Fail Check W_fields : forall (A:Type) (l:W A), W_fields_t A (W_tag A l).
Fail Check W_construct : forall (A:Type) (p: Numbers.BinNums.positive),  W_fields_t A p -> option (W A).
Fail Check W_constructP : forall (A:Type) (l:W A), W_construct A (W_tag A l) (W_fields A l) = Some l.

(* ---------------------------------------------------- *)

Inductive horror A (a : A) : forall T, T -> Type := K W w (k : horror W w) : horror W w.
Fail #[only(eqbOK)] derive horror.

(* TODO add test for fields? *)
(* ---------------------------------------------------- *)

Inductive rtree A : Type :=
  Leaf (n : A) | Node (l : list rtree).

Module XXX.
derive list.
derive rtree.
End XXX.

Fail Check XXX.rtree_is_rtree_map.
Redirect "tmp" Check XXX.rtree_tag : forall A, rtree A -> Numbers.BinNums.positive.
Redirect "tmp" Check XXX.rtree_fields_t : (Type -> Numbers.BinNums.positive -> Type).
Redirect "tmp" Check XXX.rtree_fields : forall (A:Type) (l:rtree A), XXX.rtree_fields_t A (XXX.rtree_tag A l).
Redirect "tmp" Check XXX.rtree_construct : forall (A:Type) (p: Numbers.BinNums.positive),  XXX.rtree_fields_t A p -> option (rtree A).
Redirect "tmp" Check XXX.rtree_constructP : forall (A:Type) (l:rtree A), XXX.rtree_construct A (XXX.rtree_tag A l) (XXX.rtree_fields A l) = Some l.
Redirect "tmp" Check XXX.rtree_eqb : forall (A:Type), (A -> A -> bool) -> rtree A -> rtree A -> bool.
(* bug #270 *)

#[module] derive
Inductive triv : Coverage.unit -> Prop :=
| one t : triv t | more x : triv x.

Redirect "tmp" Check triv.induction :
        forall P : (forall H : Coverage.unit, is_unit H -> triv H -> Prop),
       (forall t (Pt : is_unit t), P t Pt (one t)) ->
       (forall x (Px : is_unit x), P x Px (more x)) ->
       forall u (p : is_unit u) (s : triv u), triv.is_triv u p s -> P u p s.

(* #271 *)
derive
Inductive RoseTree : Type :=
| RT_ctr (branches : list RoseTree).

Elpi derive.param1 is_list.

#[module] derive
Inductive Pred : RoseTree -> Type :=
| Pred_ctr branches :
    is_list _ Pred branches ->
    Pred (RT_ctr branches).

Redirect "tmp" Check Pred.Pred_to_Predinv : forall T, Pred T -> Pred.Predinv T.

(* #286 *)
Module Import derive_container.
Unset Implicit Arguments.
Import XXX.
derive
Inductive wimpls {A} `{rtree A} := Kwi (x:A) (y : x = x) : wimpls | Kwa.

End derive_container.
About wimpls.wimpls.
About wimpls.Kwi.
Redirect "tmp" Check Kwi _ (refl_equal 3).

Section TestRegister.
Variable T : Type.
Definition is_T : T -> Type := fun x => True.
Definition is_T_inhab : forall x : T, is_T x := fun x => I.
Variable eqb : T -> T -> bool.
Variable eqb_correct : forall x y,eqb x y = true -> x = y.
Variable eqb_refl : forall x, eqb x x = true.

derive.eqbOK.register_axiom T is_T is_T_inhab eqb eqb_correct eqb_refl.

Inductive foo := X : T -> foo.

#[only(eqbOK),verbose] derive foo.

Redirect "tmp" Print foo_eqb_OK.

End TestRegister.

Module TestAlias.

Definition nat' := nat.
#[only(eqb_alias)] derive nat'.

Check nat'_eqb.

End TestAlias.