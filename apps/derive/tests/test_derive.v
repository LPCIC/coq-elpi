From elpi.apps Require Import derive.

From elpi.apps Require Import test_derive_stdlib.

Elpi derive Coverage.empty.
Elpi derive Coverage.unit.
Elpi derive Coverage.peano.
Elpi derive Coverage.option.
Elpi derive Coverage.pair.
Elpi derive Coverage.seq.
Elpi derive Coverage.rose.
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

Elpi derive nat.

Check nat_eq : nat -> nat -> bool.
Check nat_is_nat : nat -> Type.
Check nat_param1_nat_eq : forall x1 : nat, nat_is_nat x1 ->
                          forall x2 : nat, nat_is_nat x2 ->
                          bool_is_bool (nat_eq x1 x2).
Check nat_isk_O : nat -> bool.
Check nat_isk_S : nat -> bool.
Check nat_getk_S1 : nat -> nat -> nat.
Check nat_is_O : nat_is_nat O.
Check nat_is_S : forall x, nat_is_nat x -> nat_is_nat (S x).
Check nat_is_nat_full : forall x, nat_is_nat x.
Check nat_is_nat_functor : forall x, nat_is_nat x -> nat_is_nat x.
Check nat_induction : forall P, P 0 -> (forall n, P n -> P (S n)) -> forall x, nat_is_nat x -> P x.

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
Check list_param1_list_eq : forall A (PA : A -> Type),
                            forall f, (forall a, PA a -> forall b, PA b -> bool_is_bool (f a b)) ->
                                 forall x, list_is_list A PA x ->
                                 forall y, list_is_list A PA y ->
                                 bool_is_bool (list_eq A f x y).
      
(* ---------------------------------------------------- *)

Require Vector.

Elpi derive Vector.t Vector_.
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

(* ---------------------------------------------------- *)

Inductive W A := B (f : A -> W A).
 
Elpi derive W.
(* Not implemented yet :-/ *)
Fail Check W_induction : forall A (P : W A -> Type),
       (forall f, (forall x, UnitPred A x -> P (f x)) -> P (B A f)) ->
       forall x, P x.

(* ---------------------------------------------------- *)

Inductive horror A (a : A) : forall T, T -> Type := K W w (k : horror A a W w) : horror A a W w.

Elpi derive horror.
Fail Check horror_induction :
   forall A a (P : forall T t, horror A a T t -> Type), 
    (forall W (_: UnitPred Type W) w (_: UnitPred _ w) (k : horror A a W w), P W w k -> P W w (K A a W w k)) -> forall T t (x : horror A a T t), P T t x.

(* ---------------------------------------------------- *)

Inductive rtree A : Type :=
  Leaf (n : A) | Node (l : list (rtree A)).

Elpi derive rtree XXX.

Fail Check XXX_is_rtree_map.

(* bug #270 *)

derive
Inductive triv : Coverage.unit -> Prop :=
| one t : triv t | more x : triv x.

Check triv.induction :
        forall P : (forall H : Coverage.unit, unit_is_unit H -> triv H -> Prop),
       (forall t (Pt : unit_is_unit t), P t Pt (one t)) ->
       (forall x (Px : unit_is_unit x), P x Px (more x)) ->
       forall u (p : unit_is_unit u) (s : triv u), triv.is_triv u p s -> P u p s.
