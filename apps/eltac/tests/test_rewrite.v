From elpi.apps Require Import eltac.rewrite.

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
    elpi rewrite (@sym).
    (** [add y x = add y x /\ add y x = add y x] *)
    easy.
Defined.

End Example_rewrite.
