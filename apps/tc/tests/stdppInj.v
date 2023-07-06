From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.
From Coq Require Import Permutation.
Export ListNotations.
From Coq.Program Require Export Basics Syntax.
From elpi.apps Require Export compiler.

Notation length := Datatypes.length.
Global Generalizable All Variables.
Global Unset Transparent Obligations.

Global Unset TC_NameFullPath.

Set Warnings "+elpi".

Definition tc_opaque {A} (x : A) : A := x.
(* Typeclasses Opaque tc_opaque. *)

Global Arguments tc_opaque {_} _ /.
Declare Scope stdpp_scope.
Delimit Scope stdpp_scope with stdpp.
Global Open Scope stdpp_scope.
Notation "(=)" := eq (only parsing) : stdpp_scope.
Notation "( x =.)" := (eq x) (only parsing) : stdpp_scope.
Notation "(.= x )" := (λ y, eq y x) (only parsing) : stdpp_scope.
Notation "(≠)" := (λ x y, x ≠ y) (only parsing) : stdpp_scope.
Notation "( x ≠.)" := (λ y, x ≠ y) (only parsing) : stdpp_scope.
Notation "(.≠ x )" := (λ y, y ≠ x) (only parsing) : stdpp_scope.
Infix "=@{ A }" := (@eq A)
  (at level 70, only parsing, no associativity) : stdpp_scope.
Notation "(=@{ A } )" := (@eq A) (only parsing) : stdpp_scope.
Notation "(≠@{ A } )" := (λ X Y, ¬X =@{A} Y) (only parsing) : stdpp_scope.
Notation "X ≠@{ A } Y":= (¬X =@{ A } Y)
  (at level 70, only parsing, no associativity) : stdpp_scope.

Global Hint Extern 0 (_ = _) => reflexivity : core.
Global Hint Extern 100 (_ ≠ _) => discriminate : core.

Global Instance: ∀ A, PreOrder (=@{A}).
Proof. split; repeat intro; congruence. Qed.
Class Equiv A := equiv: relation A.
Global Instance equiv_rewrite_relation `{Equiv A} :
  RewriteRelation (@equiv A _) | 150 := {}.

Infix "≡" := equiv (at level 70, no associativity) : stdpp_scope.
Infix "≡@{ A }" := (@equiv A _)
  (at level 70, only parsing, no associativity) : stdpp_scope.

Notation "(≡)" := equiv (only parsing) : stdpp_scope.
Notation "( X ≡.)" := (equiv X) (only parsing) : stdpp_scope.
Notation "(.≡ X )" := (λ Y, Y ≡ X) (only parsing) : stdpp_scope.
Notation "(≢)" := (λ X Y, ¬X ≡ Y) (only parsing) : stdpp_scope.
Notation "X ≢ Y":= (¬X ≡ Y) (at level 70, no associativity) : stdpp_scope.
Notation "( X ≢.)" := (λ Y, X ≢ Y) (only parsing) : stdpp_scope.
Notation "(.≢ X )" := (λ Y, Y ≢ X) (only parsing) : stdpp_scope.

Notation "(≡@{ A } )" := (@equiv A _) (only parsing) : stdpp_scope.
Notation "(≢@{ A } )" := (λ X Y, ¬X ≡@{A} Y) (only parsing) : stdpp_scope.
Notation "X ≢@{ A } Y":= (¬X ≡@{ A } Y)
  (at level 70, only parsing, no associativity) : stdpp_scope.
Class LeibnizEquiv A `{Equiv A} :=
  leibniz_equiv (x y : A) : x ≡ y → x = y.
Global Hint Mode LeibnizEquiv ! - : typeclass_instances.

Global Instance: Params (@equiv) 2 := {}.
Global Instance equiv_default_relation `{Equiv A} :
  DefaultRelation (≡@{A}) | 3 := {}.
Global Hint Extern 0 (_ ≡ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡ _) => symmetry; assumption : core.


Class Inj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop :=
  inj x y : S (f x) (f y) → R x y.

Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.

Global Arguments irreflexivity {_} _ {_} _ _ : assert.
Global Arguments inj {_ _ _ _} _ {_} _ _ _ : assert.
Global Arguments inj2 {_ _ _ _ _ _} _ {_} _ _ _ _ _: assert.

Global Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 f} y : Inj R1 R3 (λ x, f x y).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.
Global Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 f} x : Inj R2 R3 (f x).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.

Notation "(∧)" := and (only parsing) : stdpp_scope.
Notation "( A ∧.)" := (and A) (only parsing) : stdpp_scope.
Notation "(.∧ B )" := (λ A, A ∧ B) (only parsing) : stdpp_scope.

Notation "(∨)" := or (only parsing) : stdpp_scope.
Notation "( A ∨.)" := (or A) (only parsing) : stdpp_scope.
Notation "(.∨ B )" := (λ A, A ∨ B) (only parsing) : stdpp_scope.

Notation "(↔)" := iff (only parsing) : stdpp_scope.
Notation "( A ↔.)" := (iff A) (only parsing) : stdpp_scope.
Notation "(.↔ B )" := (λ A, A ↔ B) (only parsing) : stdpp_scope.

Global Hint Extern 0 (_ ↔ _) => reflexivity : core.
Global Hint Extern 0 (_ ↔ _) => symmetry; assumption : core.

Notation "(→)" := (λ A B, A → B) (only parsing) : stdpp_scope.
Notation "( A →.)" := (λ B, A → B) (only parsing) : stdpp_scope.
Notation "(.→ B )" := (λ A, A → B) (only parsing) : stdpp_scope.

Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing) : stdpp_scope.
Notation "($)" := (λ f x, f x) (only parsing) : stdpp_scope.
Notation "(.$ x )" := (λ f, f x) (only parsing) : stdpp_scope.

Infix "∘" := compose : stdpp_scope.
Notation "(∘)" := compose (only parsing) : stdpp_scope.
Notation "( f ∘.)" := (compose f) (only parsing) : stdpp_scope.
Notation "(.∘ f )" := (λ g, compose g f) (only parsing) : stdpp_scope.
(** Ensure that [simpl] unfolds [id], [compose], and [flip] when fully
applied. *)
Global Arguments id _ _ / : assert.
Global Arguments compose _ _ _ _ _ _ / : assert.
Global Arguments flip _ _ _ _ _ _ / : assert.
Global Arguments const _ _ _ _ / : assert.

Definition fun_map {A A' B B'} (f: A' → A) (g: B → B') (h : A → B) : A' → B' :=
  g ∘ h ∘ f.

Global Instance id_inj {A} : Inj (=) (=) (@id A).
Proof. intros ??; auto. Qed.
Global Instance compose_inj {A B C} R1 R2 R3 (f : A → B) (g : B → C) :
  Inj R1 R2 f → Inj R2 R3 g → Inj R1 R3 (g ∘ f).
Proof. red; intuition. Qed.

(** ** Products *)
Notation "( x ,.)" := (pair x) (only parsing) : stdpp_scope.
Notation "(., y )" := (λ x, (x,y)) (only parsing) : stdpp_scope.

Notation "p .1" := (fst p) (at level 2, left associativity, format "p .1").
Notation "p .2" := (snd p) (at level 2, left associativity, format "p .2").

Definition prod_map {A A' B B'} (f: A → A') (g: B → B') (p : A * B) : A' * B' :=
  (f (p.1), g (p.2)).
Global Arguments prod_map {_ _ _ _} _ _ !_ / : assert.

Global Instance pair_inj {A B} : Inj2 (=) (=) (=) (@pair A B).
Proof. injection 1; auto. Qed.
Global Instance prod_map_inj {A A' B B'} (f : A → A') (g : B → B') :
  Inj (=) (=) f → Inj (=) (=) g → Inj (=) (=) (prod_map f g).
Proof.
  intros ?? [??] [??] ?; simpl in *; f_equal;
    [apply (inj f)|apply (inj g)]; congruence.
Qed.

Definition prod_relation {A B} (R1 : relation A) (R2 : relation B) :
  relation (A * B) := λ x y, R1 (x.1) (y.1) ∧ R2 (x.2) (y.2).

Section prod_relation.
  Context `{RA : relation A, RB : relation B}.
  Global Instance pair_inj' : Inj2 RA RB (prod_relation RA RB) pair.
  Proof. inversion_clear 1; eauto. Qed.
MySectionEnd.

Global Instance prod_equiv `{Equiv A,Equiv B} : Equiv (A * B) :=
  prod_relation (≡) (≡).
Elpi AddAllClasses.

Section prod_setoid.
  Context `{Equiv A, Equiv B}.

  Elpi Accumulate TC_solver lp:{{
    tc-Inj2 A B C RA RB RC F S :-
      RC = app [global {coq.locate "equiv"} | _],
      Res = {{prod_relation _ _}},
      coq.unify-eq RC Res ok,
      tc-Inj2 A B C RA RB Res F S.
  }}.
  Elpi Typecheck TC_solver.

  Elpi AddInstances Inj2.
  Global Instance pair_equiv_inj : Inj2 (≡) (≡) (≡@{A*B}) pair := _.
MySectionEnd.

(* Typeclasses Opaque prod_equiv. *)

(** ** Sums *)
Definition sum_map {A A' B B'} (f: A → A') (g: B → B') (xy : A + B) : A' + B' :=
  match xy with inl x => inl (f x) | inr y => inr (g y) end.
Global Arguments sum_map {_ _ _ _} _ _ !_ / : assert.

Global Instance inl_inj {A B} : Inj (=) (=) (@inl A B).
Proof. injection 1; auto. Qed.
Global Instance inr_inj {A B} : Inj (=) (=) (@inr A B).
Proof. injection 1; auto. Qed.

Global Instance sum_map_inj {A A' B B'} (f : A → A') (g : B → B') :
  Inj (=) (=) f → Inj (=) (=) g → Inj (=) (=) (sum_map f g).
Proof. intros ?? [?|?] [?|?] [=]; f_equal; apply (inj _); auto. Qed.

Inductive sum_relation {A B}
     (RA : relation A) (RB : relation B) : relation (A + B) :=
  | inl_related x1 x2 : RA x1 x2 → sum_relation RA RB (inl x1) (inl x2)
  | inr_related y1 y2 : RB y1 y2 → sum_relation RA RB (inr y1) (inr y2).

Section sum_relation.
  Context `{RA : relation A, RB : relation B}.
  Global Instance inl_inj' : Inj RA (sum_relation RA RB) inl.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance inr_inj' : Inj RB (sum_relation RA RB) inr.
  Proof. inversion_clear 1; auto. Qed.
MySectionEnd.

Global Instance sum_equiv `{Equiv A, Equiv B} : Equiv (A + B) := sum_relation (≡) (≡).

(* Elpi added here *)
Elpi Accumulate TC_solver lp:{{
  tc-Inj A B RA {{@equiv (sum _ _) (@sum_equiv _ _ _ _)}} S C :-
    tc-Inj A B RA {{sum_relation _ _}} S C.
}}.
Elpi Typecheck TC_solver.

Global Instance inl_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inl A B) := _.
Global Instance inr_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inr A B) := _.

Notation "` x" := (proj1_sig x) (at level 10, format "` x") : stdpp_scope.

(* Elpi AddInstances Inj ignoreInstances compose_inj. *)
Elpi Override TC TC_solver Only Inj.

Elpi AddAllInstances compose_inj.

Elpi Accumulate TC_solver lp:{{
  tc-Inj A B RA RB F X :-
    F = fun _ _ _, 
    G = {{@compose _ _ _ _ _}}, 
    coq.unify-eq G F ok, 
    tc-Inj A B RA RB G X.
}}.
Elpi Typecheck TC_solver.

Definition f := Nat.add 0.
Global Instance h: Inj eq eq f. 
  unfold f. simpl. easy.
Qed.

Set Warnings "+elpi".


Elpi Accumulate tc.db lp:{{
  :after "lastHook"
  tc-Inj A B RA RB F S :- 
    F = (fun _ _ _), !,
    G = {{ compose _ _ }},
    coq.unify-eq G F ok,
    tc-Inj A B RA RB G S.
}}.
Elpi Typecheck TC_solver.

Elpi Query TC_solver lp:{{
  std.forall [{{:gref compose_inj}}, {{:gref h}}] 
    (x\ sigma C\
      compile x _ _ C,
      add-tc-db _ (after "lastHook") C
    ).
}}.

Goal Inj eq eq (compose (@id nat) id).
apply _.
Qed.

Goal Inj eq eq (compose (compose (@id nat) id) id).
apply _.
Qed.

Goal Inj eq eq (fun (x:nat) => id (id x)).
apply _.
Qed.

Goal Inj eq eq (fun (x: nat) => (compose id id) (id x)).
apply (compose_inj eq eq); apply _.
Qed.