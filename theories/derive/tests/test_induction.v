From elpi Require Import derive.induction derive.param1 derive.param1P.
From Coq Require Vector.

Elpi derive.induction nat.

Check nat_induction : 
  forall P : nat -> Type,
   P O ->
   (forall n, P n -> P (S n)) ->
   forall x, P x.

Elpi derive.induction list.

Check list_induction :
  forall A : Type, forall P : list A -> Type,
    P (@nil A) ->
    (forall x : A, UnitPred A x -> forall xs : list A, P xs -> P (@cons A x xs)) ->
    forall l, P l.

Elpi derive.param1 nat.
Elpi derive.param1P natR.
Elpi derive.induction Vector.t.

Check t_induction :
  forall A : Type, forall P : forall n : nat, Vector.t A n -> Type,
    P 0 (Vector.nil A) ->
    (forall a : A, UnitPred A a -> forall n : nat, natR n ->
     forall v : Vector.t A n, P n v -> P (S n) (Vector.cons A a n v)) ->
  forall l (x : Vector.t A l), P l x.

Inductive nat1 := 
 | O (_ : bool)
 | S (_ : nat1 * (bool * list nat1)) (b : bool * bool).

Elpi derive.param1 bool.
Elpi derive.param1 list.
Elpi derive.param1 prod.
Elpi derive.param1P boolR.
Elpi derive.param1P listR.
Elpi derive.param1P prodR.
Elpi derive.induction nat1.

Check nat1_induction : forall P : nat1 -> Type,
       (forall b : bool, boolR b -> P (O b)) ->
       (forall a : nat1 * (bool * list nat1),
        prodR nat1 P (bool * list nat1) 
         (prodR bool boolR (list nat1) (listR nat1 P)) a ->
        forall b : bool * bool, prodR bool boolR bool boolR b -> P (S a b)) ->
       forall s : nat1, P s.
