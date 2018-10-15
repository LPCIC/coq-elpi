From elpi Require Import derive.param1 param1P derive.map derive.induction derive.projK derive.bcongr derive.isK derive.eq derive.eqK derive.eqcorrect derive.eqOK.

Elpi derive.param1 nat.
Elpi derive.param1P is_nat.
Elpi derive.induction nat.
Elpi derive.map is_nat.
Elpi derive.projK nat.
Elpi derive.bcongr nat.
Elpi derive.isK nat.
Elpi derive.eq nat.
Elpi derive.eqK nat.
Elpi derive.eqcorrect nat.
 
Elpi derive.eqOK nat_induction nat_ind.
Check nat_ind : forall P, P 0 -> (forall x, P x -> P (S x)) -> forall n, P n.
 
Elpi derive.eqOK nat_eq_correct nat_eqOK.
Check nat_eqOK : forall n, axiom nat nat_eq n.

Elpi derive.param1 list.
Elpi derive.param1P is_list.
Elpi derive.map is_list.
Elpi derive.induction list.
Elpi derive.projK list.
Elpi derive.bcongr list.
Elpi derive.isK list.
Elpi derive.eq list.
Elpi derive.eqK list.
Elpi derive.eqcorrect list.


Elpi derive.eqOK list_induction list_ind.
Check list_ind :
  forall (A : Type) (P : list A -> Type),
    P nil ->
    (forall H : A, forall H0 : list A, P H0 -> P (H :: H0)%list) -> forall x : list A, P x.

Elpi derive.eqOK list_eq_correct list_eqOK.
Check list_eqOK :
  forall (A : Type) (F : A -> A -> bool) x, is_list A (axiom A F) x -> axiom (list A) (list_eq A F) x.

Inductive dlist A := dnil | dcons (a : A * nat) (l : dlist A).

Elpi derive.param1 prod.
Elpi derive.param1P is_prod.
Elpi derive.map is_prod.
Elpi derive.param1 dlist.
Elpi derive.param1P is_dlist.
Elpi derive.induction dlist.
Elpi derive.projK dlist.
Elpi derive.bcongr dlist.
Elpi derive.isK dlist.
Elpi derive.map is_dlist.

Elpi derive.eq prod.
Elpi derive.induction prod.
Elpi derive.projK prod.
Elpi derive.bcongr prod.
Elpi derive.eqK prod.
Elpi derive.eqcorrect prod.

Elpi derive.eq dlist.
Elpi derive.eqK dlist. 
Elpi derive.eqcorrect dlist.

Elpi derive.eqOK dlist_induction dlist_ind2.

Check dlist_induction :
  forall (A : Type) (PA : A -> Type) (P : dlist A -> Type),
  P (dnil A) ->
  (forall a : A * nat,
   is_prod A PA nat is_nat a ->
   forall l : dlist A, P l -> P (dcons A a l)) -> forall x : dlist A, is_dlist A PA x -> P x.

Check dlist_ind2 :
   forall (A : Type) (P : dlist A -> Type),
       P (dnil A) ->
       (forall a : A * nat, forall l : dlist A, P l -> P (dcons A a l)) ->
       forall x : dlist A, P x.

Elpi derive.eqOK dlist_eq_correct dlist_eqOK.

Check dlist_eqOK : 
  forall A f l, is_dlist A (axiom A f) l -> axiom (dlist A) (dlist_eq A f) l.

