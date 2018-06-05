From elpi Require Import derive.

Elpi derive nat.

Check nat.eq : nat -> nat -> bool.
Check nat.is.O : nat -> bool.
Check nat.is.S : nat -> bool.
Check nat.map : nat -> nat.
Check nat.injection.S1 : nat -> nat -> nat.
Check nat.param1.nat : nat -> Type.
Check nat.param1.O : nat.param1.nat O.
Check nat.param1.S : forall x, nat.param1.nat x -> nat.param1.nat (S x).
Check nat.param1.natP : forall x, nat.param1.nat x.
Check nat.param1.inv.nat : nat -> Type.
Check nat.param1.inv.O : forall i, 0 = i -> nat.param1.inv.nat i.
Check nat.param1.inv.S : forall i, forall y x, y = x -> nat.param1.inv.nat x -> S y = i -> nat.param1.inv.nat i.
Check nat.param1.map : forall x, nat.param1.nat x -> nat.param1.nat x.
Check nat.induction.principle : forall P, P 0 -> (forall n, P n -> P (S n)) -> forall x, nat.param1.nat x -> P x.
Check nat.induction : forall P, P 0 -> (forall n, P n -> P (S n)) -> forall x, P x.

Elpi derive list.

Check list.eq  : forall A, (A -> A -> bool) -> list A -> list A -> bool.
Check list.is.nil  : forall A, list A -> bool.
Check list.is.cons : forall A, list A -> bool.
Check list.map : forall A B, (A -> B) -> list A -> list B.
Check list.injection.cons1 : forall A, A -> list A -> list A -> A.
Check list.injection.cons2 : forall A, A -> list A -> list A -> list A.
Check list.param1.nil : forall A P, list.param1.list A P (@nil A).
Check list.param1.cons : forall A P x (Px : P x) tl (Ptl : list.param1.list A P tl), list.param1.list A P (cons x tl).
Check list.param1.map : forall A P Q, (forall x, P x -> Q x) -> forall l, list.param1.list A P l -> list.param1.list A Q l.
Check list.induction.principle : forall A PA P, P nil -> (forall x, PA x -> forall xs, P xs -> P (cons x xs)) -> forall l, list.param1.list A PA l -> P l.
Check list.induction : forall A P, P nil -> (forall x xs, P xs -> P (cons x xs)) -> forall l, P l.

Require Vector.

Elpi derive Vector.t Vector_t.
Check Vector_t.eq : forall A, (A -> A -> bool) -> forall n, Vector.t A n -> Vector.t A n -> bool.
Check Vector_t.is.nil : forall A n, Vector.t A n -> bool.
Check Vector_t.is.cons : forall A n, Vector.t A n -> bool. 
Check Vector_t.map : forall A B, (A -> B) -> forall n, Vector.t A n -> Vector.t B n.
Check Vector_t.injection.cons1 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> A.
Check Vector_t.injection.cons2 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> nat.
Check Vector_t.injection.cons3 : forall A n, A -> forall m, Vector.t A m -> Vector.t A n -> { k : nat & Vector.t A k}.
Check Vector_t.param1.t : forall A, (A -> Type) -> forall n, nat.param1.nat n -> Vector.t A n -> Type.
Check Vector_t.param1.nil : forall A (PA : A -> Type), Vector_t.param1.t A PA 0 nat.param1.O (Vector.nil A).
Check Vector_t.param1.cons : forall A (PA : A -> Type) (a : A), PA a -> forall n (Pn : nat.param1.nat n) (H : Vector.t A n),
       Vector_t.param1.t A PA n Pn H -> Vector_t.param1.t A PA (S n) (nat.param1.S n Pn) (Vector.cons A a n H).
Check Vector_t.param1.map : forall A PA QA (H : forall x, PA x -> QA x), forall n nR v, Vector_t.param1.t A PA n nR v -> Vector_t.param1.t A QA n nR v.
Check Vector_t.induction.principle : forall A PA (P : forall n, nat.param1.nat n -> Vector.t A n -> Type), P 0 nat.param1.O (Vector.nil A) -> (forall a, PA a -> forall m mR, forall (v : Vector.t A m), P m mR v -> P (S m) (nat.param1.S m mR) (Vector.cons A a m v)) -> forall n nR v, Vector_t.param1.t A PA n nR v -> P n nR v.
(* FIXME *)
Fail Check Vector_t.induction : forall A (P : forall n, Vector.t A n -> Type), P 0 (Vector.nil A) -> (forall a m (v : Vector.t A m), P m v -> P (S m) (Vector.cons A a m v)) -> forall n v, P n v.


Inductive W A := B (f : A -> W A).
 
(* FIXME *)
Fail Elpi derive W.
Fail Check W.induction : forall A (P : W A -> Type),
       (forall f, (forall x, UnitPred A x -> P (f x)) -> P (B A f)) ->
       forall x, P x.

Inductive horror A (a : A) : forall T, T -> Type := K W w (k : horror A a W w) : horror A a W w.

(* FIXME *)
Fail Elpi derive horror.
Fail Check horror.induction.principle :
   forall A a (P : forall T t, horror A a T t -> Type), 
    (forall W (_: UnitPred Type W) w (_: UnitPred _ w) (k : horror A a W w), P W w k -> P W w (K A a W w k)) -> forall T t (x : horror A a T t), P T t x.
Fail Check horror.induction :
   forall A a (P : forall T t, horror A a T t -> Type), 
    (forall W w (k : horror A a W w), P W w k -> P W w (K A a W w k)) -> forall T t (x : horror A a T t), P T t x.

