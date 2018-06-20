From elpi Require Import test_derive_stdlib derive.projK derive.bcongr.

Module Coverage.
Elpi derive.projK Coverage.empty.
Elpi derive.projK Coverage.unit.
Elpi derive.projK Coverage.peano.
Elpi derive.projK Coverage.option.
Elpi derive.projK Coverage.pair.
Elpi derive.projK Coverage.seq.
Elpi derive.projK Coverage.tree.
Elpi derive.projK Coverage.nest.
Elpi derive.projK Coverage.w.
Elpi derive.projK Coverage.vect.
Elpi derive.projK Coverage.dyn.
Elpi derive.projK Coverage.zeta.
Elpi derive.projK Coverage.beta.
Elpi derive.projK Coverage.iota.
Elpi derive.projK Coverage.large.

Elpi derive.bcongr Coverage.empty.
Elpi derive.bcongr Coverage.unit.
Elpi derive.bcongr Coverage.peano.
Elpi derive.bcongr Coverage.option.
Elpi derive.bcongr Coverage.pair.
Elpi derive.bcongr Coverage.seq.
Elpi derive.bcongr Coverage.tree.
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

Check true_congr : reflect (true = true) true.
Check false_congr : reflect (false = false) true.

Elpi derive.bcongr nat.

Check O_congr : reflect (0 = 0) true.
Check S_congr : forall x y b, reflect (x = y) b -> reflect (S x = S y) b.

Elpi derive.bcongr prod.

Check pair_congr :
  forall A B,
  forall (x1 x2 : A) b1, reflect (x1 = x2) b1 ->
  forall (y1 y2 : B) b2, reflect (y1 = y2) b2 ->
    reflect ((x1,y1) = (x2,y2)) (b1 && b2).

Elpi derive.bcongr list.

Check nil_congr : forall A, reflect (@nil A = nil) true.
Check cons_congr :
  forall A,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (xs ys : list A) b2, reflect (xs = ys) b2 ->
    reflect (@cons A x xs = cons y ys) (b1 && b2).

Inductive trlist A B :=
  nil3 | cons3 (a : A) (b : B) (t : trlist A B).

Elpi derive.projK trlist.
Elpi derive.bcongr trlist.

Check nil3_congr : forall A B, reflect (nil3 A B = nil3 A B) true.
Check cons3_congr :
  forall A B,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (a b : B) b2, reflect (a = b) b2 ->
  forall (l1 l2 : trlist A B) b3, reflect (l1 = l2) b3 ->
    reflect (cons3 A B x a l1 = cons3 A B y b l2) (b1 && (b2 && b3)).


Inductive nuparam A := K : A -> nuparam (A * A)%type -> nuparam A.

Elpi derive.projK nuparam.
Elpi derive.bcongr nuparam.