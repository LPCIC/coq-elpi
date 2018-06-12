From elpi Require Import derive.param1 derive.map derive.induction derive.projK derive.bcongr derive.isK derive.eq derive.eqK derive.eqOK derive.constsimplifier.

Elpi derive.param1 nat.
Elpi derive.param1P natR.
Elpi derive.induction nat.
Elpi derive.map natR.
Elpi derive.projK nat.
Elpi derive.bcongr nat.
Elpi derive.isK nat.
Elpi derive.eq nat.
Elpi derive.eqK nat.
Elpi derive.eqOK nat.

Elpi derive.constsimplifier nat_induction nat_ind.
Check nat_ind : forall P, P 0 -> (forall x, P x -> P (S x)) -> forall n, P n.

Elpi derive.constsimplifier nat_eqOK nat_eqOKsimple.
Check nat_eqOKsimple : forall n, axiom nat nat_eq n.

Elpi derive.param1 list.
Elpi derive.param1P listR.
Elpi derive.map listR.
Elpi derive.induction list.
Elpi derive.projK list.
Elpi derive.bcongr list.
Elpi derive.isK list.
Elpi derive.eq list.
Elpi derive.eqK list.
Elpi derive.eqOK list.


Elpi derive.constsimplifier list_induction list_ind.
Check list_ind :
  forall (A : Type) (P : list A -> Type),
    P nil ->
    (forall H : A, forall H0 : list A, P H0 -> P (H :: H0)%list) -> forall x : list A, P x.

Elpi derive.constsimplifier list_eqOK list_eqOKsimple.
Check list_eqOKsimple :
  forall (A : Type) (F : A -> A -> bool) x, listR A (axiom A F) x -> axiom (list A) (list_eq A F) x.

Inductive dlist A := dnil | dcons (a : A * nat) (l : dlist A).

Elpi derive.param1 prod.
Elpi derive.param1P prodR.
Elpi derive.map prodR.
Elpi derive.param1 dlist.
Elpi derive.param1P dlistR.
Elpi derive.induction dlist.
Elpi derive.projK dlist.
Elpi derive.bcongr dlist.
Elpi derive.isK dlist.
Elpi derive.map dlistR.

Elpi derive.eq prod.
Elpi derive.induction prod.
Elpi derive.projK prod.
Elpi derive.bcongr prod.
Elpi derive.eqK prod.
Elpi derive.eqOK prod.

Elpi derive.eq dlist.
Elpi derive.eqK dlist.
Elpi derive.eqOK dlist.

Elpi derive.constsimplifier dlist_induction dlist_ind2.

Check dlist_induction :
  forall (A : Type) (PA : A -> Type) (P : dlist A -> Type),
  P (dnil A) ->
  (forall a : A * nat,
   prodR A PA nat natR a ->
   forall l : dlist A, P l -> P (dcons A a l)) -> forall x : dlist A, dlistR A PA x -> P x.

Check dlist_ind2 :
   forall (A : Type) (P : dlist A -> Type),
       P (dnil A) ->
       (forall a : A * nat, forall l : dlist A, P l -> P (dcons A a l)) ->
       forall x : dlist A, P x.

Elpi derive.constsimplifier dlist_eqOK dlist_eqOKsimple.

Check dlist_eqOKsimple : 
  forall A f l, dlistR A (axiom A f) l -> axiom (dlist A) (dlist_eq A f) l.

