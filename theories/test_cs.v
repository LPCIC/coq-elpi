From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

Theorem fg_equal :
  forall (A B : Type) (f g : A -> B) (x y : A),
    x = y -> f = g -> f x = g y.
Proof.
  intros A B f g x y Hxy Hfg.
  rewrite <- Hxy. rewrite <- Hfg.
  reflexivity.
Qed.

Definition eq_ok (A : Type) (eq : A -> A -> bool) (a b : A) :=
  (eq a b = true <-> a = b).
Elpi Accumulate File "eq.elpi".

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

Import DecEq.theory.

Fail Check 3 ~~ 3.
Elpi Run "create-eq-with-proof ""nat"".".
Definition nat_DecEq : DecEq.class nat := DecEq.Class nat_equal nat_equal_ok.
Canonical Structure nat_DecEqCS : DecEq.type := DecEq.Pack nat nat_DecEq.
Check (3 ~~ 3).
Eval compute in 3 ~~ 3.
Eval compute in 3 ~~ 4.
Check @DecEq.op.

Theorem DecideEquality : forall (E : DecEq.type) (a b : DecEq.obj E),
  { a = b } + { a <> b }.
Proof.
  intros E a b. destruct E. destruct class_of. destruct (cmp a b) eqn:Hcmp.
  - left. apply proof. assumption.
  - right. intro Heq. apply proof in Heq. rewrite -> Hcmp in Heq. inversion Heq.
Qed.
Arguments DecideEquality {E} a b.
Check DecideEquality.

Lemma DecEqNat : forall (a b : nat), {a = b} + {a <> b}.
Proof. exact DecideEquality. Qed.

Example DecEq45 : { 4 = 5 } + { 4 <> 5 }.
Proof. apply DecideEquality. Qed.

Elpi Run "create-eq-from-name ""list"".".
Theorem list_equal_ok : forall (E : DecEq.type) (a b : list (DecEq.obj E)),
  list_equal (DecEq.obj E) (DecEq.op) a b = true <-> a = b.
Proof. intros E a.
  induction a.
  { intro b. destruct b.
    - simpl. split. { intro H. reflexivity. } { intro H. reflexivity. }
    - simpl. split.
      + intro H. inversion H.
      + intro H. inversion H.
  }
  { intro b. destruct b.
    - simpl. split. { intro H. inversion H. } { intro H. inversion H. }
    - simpl. split.
      + intro H. apply andb_prop in H. destruct H. apply DecEq.op_ok in H0. rewrite -> H0.
        apply IHa in H. rewrite -> H. reflexivity.
      + intro H. apply andb_true_intro. split.
        * apply IHa. inversion H. reflexivity.
        * apply DecEq.op_ok. inversion H. reflexivity.
  }
Qed.

Definition list_DecEq (E : DecEq.type) := DecEq.Class (list_equal (DecEq.obj E) (DecEq.op)) (list_equal_ok E).
Canonical Structure list_DecEqCS (E : DecEq.type) : DecEq.type :=
  DecEq.Pack (list (DecEq.obj E)) (list_DecEq E).

Lemma DecEqListNat : forall (a b : list nat), { a = b } + { a <> b }.
Proof. exact DecideEquality. Qed.

Inductive awful (A B : Type) : Type :=
| mkawful : awful (list B) A -> A -> awful A B
| awful_nil : B -> awful A B.
Check @awful_ind.

(* Theorem awful_ind_2 : forall (S : Type) (p : S -> Type) (l_list : S -> S) (pr_list : forall s : S, p (l_list s) = list (p s)),
  forall P : forall (A B : S), awful (p A) (p B) -> Prop,
  (forall (A B : S) (a : awful (p (l_list B)) (p A)), P (l_list B) A a -> forall x : p A, P A B (mkawful (p A) (p B) a x)) ->
  (forall (A B : S) (b : p B), P A B (awful_nil (p A) (p B) b)) ->
  forall (A B : S) (a : awful (p A) (p B)), P A B a.
*)

Fixpoint awful_equal {A B : DecEq.type} (a b : awful (DecEq.obj A) (DecEq.obj B)) : bool :=
match a with
| mkawful _ _ a' x => match  b with
                      | mkawful _ _ b' y => (awful_equal a' b') && (x ~~ y)
                      | awful_nil _ _ _ => false
                      end
| awful_nil _ _ x => match b with
                     | mkawful _ _ _ _ => false
                     | awful_nil _ _ y => x ~~ y
                     end
end.
About eq_ind.

Fixpoint awful_equal_ok (A B : DecEq.type) (a b : awful (DecEq.obj A) (DecEq.obj B))
    : awful_equal a b = true <-> a = b :=
let A' := DecEq.obj A in let B' := DecEq.obj B in
match a with
| mkawful _ _ a' x => match b with

  | mkawful _ _ b' y => conj (fun H : andb (awful_equal a' b') (x ~~ y) = true => match (andb_prop _ _ H) with
    | conj Haw Ha => fg_equal A' (awful A' B') (mkawful A' B' a') (mkawful A' B' b') x y
      (proj1 (iff_and (DecEq.op_ok x y)) Ha)
      (fg_equal (awful (list B') A') (A' -> awful A' B') (mkawful A' B') (mkawful A' B') a' b'
        (proj1 (iff_and (awful_equal_ok _ _ a' b')) Haw)
        eq_refl
      )
    end)
    (fun H : mkawful A' B' a' x = mkawful A' B' b' y =>
      andb_true_intro (conj
        (proj2 (iff_and (awful_equal_ok _ _ a' b')) (f_equal (fun z => match z with | mkawful _ _ y _ => y | awful_nil _ _ _ => a' end) H))
        (proj2 (iff_and (DecEq.op_ok x y)) (f_equal (fun z => match z with | mkawful _ _ _ y => y | awful_nil _ _ _ => x end) H))
      )
    )

  | awful_nil _ _ y => conj (fun H : false = true => (False_ind (mkawful _ _ a' x = awful_nil _ _ y)
      (eq_ind false (fun b : bool => match b with | true => False | false => True end) I true H)))
    (fun H : mkawful A' B' a' x = awful_nil A' B' y => False_ind (false = true)
      (eq_ind (mkawful A' B' a' x) (fun z : awful A' B' => match z with | mkawful _ _ _ _ => True | awful_nil _ _ _ => False end) I (awful_nil A' B' y) H))
  end

| awful_nil _ _ x => match b with

  | mkawful _ _ b' y => conj (fun H : false = true => (False_ind (awful_nil _ _ x = mkawful _ _ b' y)
      (eq_ind false (fun b : bool => match b with | true => False | false => True end) I true H)))
    (fun H : awful_nil A' B' x = mkawful A' B' b' y => (False_ind (false = true)
      (eq_ind (awful_nil A' B' x) (fun x => match x with | mkawful _ _ _ _ => False | awful_nil _ _ _ => True end) I (mkawful A' B' b' y) H)))

  | awful_nil _ _ y => conj (fun H : x ~~ y = true =>
    (fg_equal B' (awful A' B') (awful_nil A' B') (awful_nil A' B') x y
      (proj1 (iff_and (DecEq.op_ok x y)) H)
      eq_refl
    ))
    (fun H : awful_nil A' B' x = awful_nil A' B' y =>
      (proj2 (iff_and (DecEq.op_ok x y)) (f_equal (fun z => match z with | mkawful _ _ _ _ => x | awful_nil _ _ y => y end) H))
    )
  end
end.
Check awful_equal_ok.

Elpi Run "coq-say {{DecEq.op}}.".

