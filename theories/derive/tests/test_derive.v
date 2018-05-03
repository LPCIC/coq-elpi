From elpi Require Import derive.

Elpi derive nat.

Check nat.eq : nat -> nat -> bool.
Check nat.is.O : nat -> bool.
Check nat.is.S : nat -> bool.
Fail Check nat.map : nat -> nat.
Check nat.injection.S1 : nat -> nat -> nat.
Check nat.param1.nat : nat -> Type.
Check nat.param1.O : nat.param1.nat O.
Check nat.param1.S : forall x, nat.param1.nat x -> nat.param1.nat (S x).
Check nat.induction.principle : forall P, P 0 -> (forall n, P n -> P (S n)) -> forall x, P x.
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
Check list.induction.principle : forall A P, P nil -> (forall x, elpi.derive.induction.UnitPred A x -> forall xs, P xs -> P (cons x xs)) -> forall l, P l.
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
Check Vector_t.induction.principle : forall A (P : forall n, Vector.t A n -> Type), P 0 (Vector.nil A) -> (forall a, elpi.derive.induction.UnitPred A a -> forall m, nat.param1.nat m -> forall (v : Vector.t A m), P m v -> P (S m) (Vector.cons A a m v)) -> forall n v, P n v.
Check Vector_t.induction : forall A (P : forall n, Vector.t A n -> Type), P 0 (Vector.nil A) -> (forall a m (v : Vector.t A m), P m v -> P (S m) (Vector.cons A a m v)) -> forall n v, P n v.

Definition arrow A B := A -> B.
Elpi derive.param1 arrow.
Print arrowR.

Definition cons A := A -> list A -> list A.
Elpi derive.param1 cons.
Print consR.

(*
Inductive W A := B (f : A -> W A).
Print W_ind.
Elpi derive W.
*)

Inductive horror A (a : A) : forall T, T -> Type := K W w (k : horror A a W w) : horror A a W w.
 
Elpi derive horror.

