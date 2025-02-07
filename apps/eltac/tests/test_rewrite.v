From elpi.apps Require Import eltac.rewrite.

Axiom add_comm : forall x y, x + y = y + x.
Axiom mul_comm : forall x y, x * y = y * x.

Goal (forall x : nat, 1 + x = x + 1) -> 
    forall y,  2 * ((y+y) + 1) = ((y + y)+1) * 2.
Proof.
    intro H. 
    intro x.
    eltac.rewrite H.
    eltac.rewrite mul_comm.
    exact eq_refl.
Defined.

Section Example_rewrite.
Variable A : Type.
Variable B : A -> Type.
Variable C : forall (a : A) (b : B a), Type.
Variable add : forall {a : A} {b : B a}, C a b -> C a b -> C a b.
Variable sym : forall {a : A} {b : B a} (c c' : C a b), add c c' = add c' c.

Goal forall (a : A) (b : B a) (x y : C a b),
    add x y = add y x /\ add x y = add y x.
Proof.
    intros a b x y.
    eltac.rewrite @sym. (* @sym is a gref *)
    (** [add y x = add y x /\ add y x = add y x] *)
    easy.
Defined.

Goal forall (a : A) (b : B a) (x y : C a b),
    add x y = add y x /\ add x y = add y x.
Proof.
    intros a b x y.
    eltac.rewrite sym. (* because of implicit arguments, this is sym _ _, which is a term *)
   easy.
Defined.

Goal forall n, 2 * n = n * 2.
Proof.
    intro n.
    Fail eltac.rewrite add_comm.
    eltac.rewrite add_comm "strong".
    Abort.

End Example_rewrite.
