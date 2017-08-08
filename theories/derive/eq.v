Require Import elpi.

(* Support lemmas *)

Theorem congr (A B : Type) (f g : A -> B) (x y : A) :
    x = y -> f = g -> f x = g y.
Proof. now intros Hxy Hfg; rewrite Hxy, Hfg. Qed.

Definition eq_ok (A : Type) (eq : A -> A -> bool) (a b : A) :=
  (eq a b = true <-> a = b).

Module DecEq.
  Record class (T : Type) := Class { cmp : T -> T -> bool;
                                     proof : forall (a b : T), cmp a b = true <-> a = b }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> bool :=
    let 'Pack _ (Class _ cmp _) := e in cmp.
  Definition op_ok (e : type) : forall (a b : obj e), op e a b = true <-> a = b :=
    let 'Pack _ (Class _ _ proof) := e in proof.
  Arguments op {e} x y : simpl never.
  Arguments op_ok {e} : simpl never.
  Arguments Class {T} cmp proof.
  Module theory.
    Notation "x ~~ y" := (op x y) (at level 70).
  End theory.
End DecEq.

Elpi Program derive.eq.
Elpi Accumulate File "coq-derive-eq.elpi".

Elpi Accumulate "
  main []     :- derive-deceq ""t"". % ppx convention
  main [Name] :- derive-deceq Name.
".
