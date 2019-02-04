From elpi Require Import derive.projK derive.bcongr.

From elpi Require Import test_derive_stdlib test_projK.

Module Coverage.
Elpi derive.bcongr Coverage.empty.
Elpi derive.bcongr Coverage.unit.
Elpi derive.bcongr Coverage.peano.
Elpi derive.bcongr Coverage.option.
Elpi derive.bcongr Coverage.pair.
Elpi derive.bcongr Coverage.seq.
Elpi derive.bcongr Coverage.rose.
Elpi derive.bcongr Coverage.nest.
Elpi derive.bcongr Coverage.w.
Fail Elpi derive.bcongr Coverage.vect.
Fail Elpi derive.bcongr Coverage.dyn.
Elpi derive.bcongr Coverage.zeta.
Elpi derive.bcongr Coverage.beta.
Fail Elpi derive.bcongr Coverage.iota.
Elpi derive.bcongr Coverage.large.
End Coverage.


Elpi derive.projK nat.
Elpi derive.projK bool.
Elpi derive.projK list.
Elpi derive.projK prod.

Elpi derive.bcongr bool.

Check bool_bcongr_true : reflect (true = true) true.
Check bool_bcongr_false : reflect (false = false) true.

Elpi derive.bcongr nat.

Check nat_bcongr_O : reflect (0 = 0) true.
Check nat_bcongr_S : forall x y b, reflect (x = y) b -> reflect (S x = S y) b.

Elpi derive.bcongr prod.

Check prod_bcongr_pair :
  forall A B,
  forall (x1 x2 : A) b1, reflect (x1 = x2) b1 ->
  forall (y1 y2 : B) b2, reflect (y1 = y2) b2 ->
    reflect ((x1,y1) = (x2,y2)) (b1 && b2).

Elpi derive.bcongr list.

Check list_bcongr_nil : forall A, reflect (@nil A = nil) true.
Check list_bcongr_cons :
  forall A,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (xs ys : list A) b2, reflect (xs = ys) b2 ->
    reflect (@cons A x xs = cons y ys) (b1 && b2).

Inductive trlist A B :=
  nil3 | cons3 (a : A) (b : B) (t : trlist A B).

Elpi derive.projK trlist.
Elpi derive.bcongr trlist.

Check trlist_bcongr_nil3 : forall A B, reflect (nil3 A B = nil3 A B) true.
Check trlist_bcongr_cons3 :
  forall A B,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (a b : B) b2, reflect (a = b) b2 ->
  forall (l1 l2 : trlist A B) b3, reflect (l1 = l2) b3 ->
    reflect (cons3 A B x a l1 = cons3 A B y b l2) (b1 && (b2 && b3)).


Inductive nuparam A := K : A -> nuparam (A * A)%type -> nuparam A.

Elpi derive.projK nuparam.
Elpi derive.bcongr nuparam.
