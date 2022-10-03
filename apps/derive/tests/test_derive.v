From elpi.apps Require Import derive.std derive.legacy derive.experimental.
From elpi.apps Require Import test_derive_stdlib.

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

Check nat_eq : nat -> nat -> bool.
Check nat_is_nat : nat -> Type.
Check nat_isk_O : nat -> bool.
Check nat_isk_S : nat -> bool.
Check nat_getk_S1 : nat -> nat -> nat.
Check nat_is_O : nat_is_nat O.
Check nat_is_S : forall x, nat_is_nat x -> nat_is_nat (S x).
Check nat_is_nat_full : forall x, nat_is_nat x.
Check nat_is_nat_functor : forall x, nat_is_nat x -> nat_is_nat x.
Check nat_induction : forall P, P 0 -> (forall n, P n -> P (S n)) -> forall x, nat_is_nat x -> P x.

Check nat_tag : nat -> Numbers.BinNums.positive.
Check nat_fields_t : Numbers.BinNums.positive -> Type. 
Check nat_fields : forall (n:nat), nat_fields_t (nat_tag n). 
Check nat_construct : forall (p: Numbers.BinNums.positive),  nat_fields_t p -> option nat.
Check nat_constructP : forall (n:nat), nat_construct (nat_tag n) (nat_fields n) = Some n.
Check nat_eqb : nat -> nat -> bool.
Check nat_eqb_correct. 
Check nat_eqb_refl.
(* ---------------------------------------------------- *)

Elpi derive.param1 andb.

Elpi derive list.

Check list_eq  : forall A, (A -> A -> bool) -> list A -> list A -> bool.
Check list_isk_nil  : forall A, list A -> bool.
Check list_isk_cons : forall A, list A -> bool.
Check list_map : forall A B, (A -> B) -> list A -> list B.
Check list_getk_cons1 : forall A, A -> list A -> list A -> A.
Check list_getk_cons2 : forall A, A -> list A -> list A -> list A.
Check list_is_nil : forall A P, list_is_list A P (@nil A).
Check list_is_cons : forall A P x (Px : P x) tl (Ptl : list_is_list A P tl), list_is_list A P (cons x tl).
Check list_is_list_functor : forall A P Q, (forall x, P x -> Q x) -> forall l, list_is_list A P l -> list_is_list A Q l.
Check list_induction : forall A PA P, P nil -> (forall x, PA x -> forall xs, P xs -> P (cons x xs)) -> forall l, list_is_list A PA l -> P l.
Check list_tag : forall A, list A -> Numbers.BinNums.positive.
Check list_fields_t : (Type -> Numbers.BinNums.positive -> Type). 
Check list_fields : forall (A:Type) (l:list A), list_fields_t A (list_tag A l). 
Check list_construct : forall (A:Type) (p: Numbers.BinNums.positive),  list_fields_t A p -> option (list A).
Check list_constructP : forall (A:Type) (l:list A), list_construct A (list_tag A l) (list_fields A l) = Some l.
Check list_eqb : forall A, (A -> A -> bool) -> list A -> list A -> bool.
Check list_eqb_correct.   
Check list_eqb_refl.      
(* ---------------------------------------------------- *)

Require Vector.

Elpi derive Vector.t Vector.
Check Vector_eq : forall A, (A -> A -> bool) -> forall n, Vector.t A n -> Vector.t A n -> bool.
Check Vector_isk_nil : forall A n, Vector.t A n -> bool.
Check Vector_isk_cons : forall A n, Vector.t A n -> bool. 
Check Vector_map : forall A B, (A -> B) -> forall n, Vector.t A n -> Vector.t B n.
Check Vector_getk_cons1 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> A.
Check Vector_getk_cons2 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> nat.
Check Vector_getk_cons3 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> { k : nat & Vector.t A k}.
Check Vector_is_t : forall A, (A -> Type) -> forall n, nat_is_nat n -> Vector.t A n -> Type.
Check Vector_is_nil : forall A (PA : A -> Type), Vector_is_t A PA 0 nat_is_O (Vector.nil A).
Check Vector_is_cons : forall A (PA : A -> Type) (a : A), PA a -> forall n (Pn : nat_is_nat n) (H : Vector.t A n),
       Vector_is_t A PA n Pn H -> Vector_is_t A PA (S n) (nat_is_S n Pn) (Vector.cons A a n H).
Check Vector_is_t_functor : forall A PA QA (H : forall x, PA x -> QA x), forall n nR v, Vector_is_t A PA n nR v -> Vector_is_t A QA n nR v.
Check Vector_induction : forall A PA (P : forall n, nat_is_nat n -> Vector.t A n -> Type), P 0 nat_is_O (Vector.nil A) -> (forall a, PA a -> forall m mR, forall (v : Vector.t A m), P m mR v -> P (S m) (nat_is_S m mR) (Vector.cons A a m v)) -> forall n nR v, Vector_is_t A PA n nR v -> P n nR v.
Check Vector_tag : forall A i, Vector.t A i -> Numbers.BinNums.positive.
Fail Check Vector_fields_t : (Type -> Numbers.BinNums.positive -> Type). 
Fail Check Vector_fields : forall (A:Type) (n:nat) (l:Vector.t A n), Vector_fields_t A (Vector_tag A l). 
Fail Check Vector_construct : forall (A:Type) (p: Numbers.BinNums.positive),  Vector_fields_t A p -> option (Vector A).
Fail Check Vector_constructP : forall (A:Type) (l:Vector.t A), Vector_construct A (Vector_tag A l) (Vector_fields A l) = Some l.
Fail Check Vector_eqb : forall A, (A -> A -> bool) -> forall n, Vector.t A n -> Vector.t A n -> bool.

(* ---------------------------------------------------- *)

Inductive W A := B (f : A -> W).
 
Elpi derive W.
(* Not implemented yet :-/ *)
Fail Check W_induction : forall A (P : W A -> Type),
       (forall f, (forall x, UnitPred A x -> P (f x)) -> P (B A f)) ->
       forall x, P x.
Check W_tag : forall A, W A -> Numbers.BinNums.positive.
Fail Check W_fields_t : (Type -> Numbers.BinNums.positive -> Type). 
Fail Check W_fields : forall (A:Type) (l:W A), W_fields_t A (W_tag A l). 
Fail Check W_construct : forall (A:Type) (p: Numbers.BinNums.positive),  W_fields_t A p -> option (W A).
Fail Check W_constructP : forall (A:Type) (l:W A), W_construct A (W_tag A l) (W_fields A l) = Some l.

(* ---------------------------------------------------- *)

Inductive horror A (a : A) : forall T, T -> Type := K W w (k : horror W w) : horror W w.

Elpi derive horror.
Fail Check horror_induction :
   forall A a (P : forall T t, horror A a T t -> Type), 
    (forall W (_: UnitPred Type W) w (_: UnitPred _ w) (k : horror A a W w), P W w k -> P W w (K A a W w k)) -> forall T t (x : horror A a T t), P T t x.
Check horror_tag : forall A a T t, horror A a T t -> Numbers.BinNums.positive.

(* TODO add test for fields? *)
(* ---------------------------------------------------- *)

Inductive rtree A : Type :=
  Leaf (n : A) | Node (l : list rtree).

Elpi derive rtree XXX.

Fail Check XXX_is_rtree_map.
Check XXX_tag : forall A, rtree A -> Numbers.BinNums.positive.
Check XXX_fields_t : (Type -> Numbers.BinNums.positive -> Type). 
Check XXX_fields : forall (A:Type) (l:rtree A), XXX_fields_t A (XXX_tag A l). 
Check XXX_construct : forall (A:Type) (p: Numbers.BinNums.positive),  XXX_fields_t A p -> option (rtree A).
Check XXX_constructP : forall (A:Type) (l:rtree A), XXX_construct A (XXX_tag A l) (XXX_fields A l) = Some l.
Check XXX_eqb : forall (A:Type), (A -> A -> bool) -> rtree A -> rtree A -> bool.
(* bug #270 *)

derive
Inductive triv : Coverage.unit -> Prop :=
| one t : triv t | more x : triv x.

Check triv.induction :
        forall P : (forall H : Coverage.unit, unit_is_unit H -> triv H -> Prop),
       (forall t (Pt : unit_is_unit t), P t Pt (one t)) ->
       (forall x (Px : unit_is_unit x), P x Px (more x)) ->
       forall u (p : unit_is_unit u) (s : triv u), triv.is_triv u p s -> P u p s.
     
(* #271 *)
derive
Inductive RoseTree : Type :=
| RT_ctr (branches : list RoseTree).

Elpi derive.param1 list_is_list.

derive
Inductive Pred : RoseTree -> Type :=
| Pred_ctr branches :
    list_is_list _ Pred branches ->
    Pred (RT_ctr branches).

Check Pred.Pred_to_Predinv : forall T, Pred T -> Pred.Predinv T.

(* #286 *)
derive
Inductive wimpls {A} `{rtree A} := Kwi (x:A) (y : x = x) : wimpls | Kwa.
About wimpls.wimpls.
About wimpls.Kwi.
Check Kwi _ (refl_equal 3).
