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
 
Elpi derive.eqOK nat nat_eqOK.
Check nat_eqOK : forall n, eq_axiom nat nat_eq n.

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

Elpi derive.eqOK list list_eqOK.
Check list_eqOK :
  forall (A : Type) (F : A -> A -> bool)
    (H : forall l, eq_axiom A F l) x,
      eq_axiom (list A) (list_eq A F) x.

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

Elpi derive.eqOK dlist dlist_eqOK.

Check dlist_eqOK : 
  forall A f (h : forall l, eq_axiom A f l) l,
    eq_axiom (dlist A) (dlist_eq A f) l.

