From elpi Require Import derive.induction derive.param1 derive.param1P.
From Coq Require Vector.

Elpi derive.param1 nat.
Elpi derive.induction nat.

Check nat_induction : 
  forall P : nat -> Type,
   P O ->
   (forall n, P n -> P (S n)) ->
   forall x, natR x -> P x.

Elpi derive.param1 list.
Elpi derive.induction list.

Check list_induction :
  forall (A : Type) (PA : A -> Type) (P : list A -> Type),
    P (@nil A) ->
    (forall x : A, PA x -> forall xs : list A, P xs -> P (@cons A x xs)) ->
    forall l, listR A PA l -> P l.

Elpi derive.param1P natR.

Module V.
Include Vector.
Elpi derive.param1 t.
Elpi derive.induction Vector.t "induction".
End V.

Check V.induction :
  forall A (PA : A -> Type) (P : forall n : nat, natR n -> V.t A n -> Type),
    P 0 OR (Vector.nil A) ->
    (forall a : A, PA a -> forall n : nat, forall nR: natR n,
     forall v : V.t A n, P n nR v -> P (S n) (SR n nR) (V.cons A a n v)) ->
  forall l lR (x : V.t A l), V.tR A PA l lR x -> P l lR x.

Module N.
Inductive nat1 := 
 | O (_ : bool)
 | S (_ : nat1 * (bool * list nat1)) (b : bool * bool).

Elpi derive.param1 bool.
Elpi derive.param1 prod.
Elpi derive.param1P boolR.
Elpi derive.param1P listR.
Elpi derive.param1P prodR.

Elpi derive.param1 nat1.
Elpi derive.induction nat1.

Check nat1_induction : 
     forall (P : nat1 -> Type),
       (forall b : bool, boolR b -> P (O b)) ->
       (forall x : nat1 * (bool * list nat1),
        prodR nat1 P (bool * list nat1) (prodR bool boolR (list nat1) (listR nat1 P)) x ->
        forall b : bool * bool, prodR bool boolR bool boolR b -> P (S x b)) ->
       forall n : nat1, nat1R n -> P n.
End N.


Inductive tree := Leaf | Node : list tree -> tree.

About tree_ind.

Elpi derive.param1 list _Forall.     About list_Forall. 
Elpi derive.param1P list_Forall. 
Elpi derive.param1 tree.
Elpi derive.induction tree.           About tree_induction.



