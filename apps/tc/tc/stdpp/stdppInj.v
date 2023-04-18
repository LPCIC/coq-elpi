From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.
From Coq Require Import Permutation.
Export ListNotations.
From Coq.Program Require Export Basics Syntax.
From elpi.apps.tc Require Import compiler.

Notation length := Datatypes.length.
Global Generalizable All Variables.
Global Unset Transparent Obligations.
Obligation Tactic := idtac.
Add Search Blacklist "_obligation_".
Add Search Blacklist "_unseal".
Section seal.
  Local Set Primitive Projections.
  Record seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
Elpi myEnd.
Global Arguments unseal {_ _} _ : assert.
Global Arguments seal_eq {_ _} _ : assert.
Ltac tc_solve :=
  solve [once (typeclasses eauto)].
Definition tc_opaque {A} (x : A) : A := x.
Typeclasses Opaque tc_opaque.
Global Arguments tc_opaque {_} _ /.
Declare Scope stdpp_scope.
Delimit Scope stdpp_scope with stdpp.
Global Open Scope stdpp_scope.
Notation "'True'" := True (format "True") : type_scope.
Notation "'False'" := False (format "False") : type_scope.
Notation "'forall' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   only parsing) : type_scope.
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

Lemma leibniz_equiv_iff `{LeibnizEquiv A, !Reflexive (≡@{A})} (x y : A) :
  x ≡ y ↔ x = y.
Proof. split; [apply leibniz_equiv|]. intros ->; reflexivity. Qed.

Ltac fold_leibniz := repeat
  match goal with
  | H : context [ _ ≡@{?A} _ ] |- _ =>
    setoid_rewrite (leibniz_equiv_iff (A:=A)) in H
  | |- context [ _ ≡@{?A} _ ] =>
    setoid_rewrite (leibniz_equiv_iff (A:=A))
  end.
Ltac unfold_leibniz := repeat
  match goal with
  | H : context [ _ =@{?A} _ ] |- _ =>
    setoid_rewrite <-(leibniz_equiv_iff (A:=A)) in H
  | |- context [ _ =@{?A} _ ] =>
    setoid_rewrite <-(leibniz_equiv_iff (A:=A))
  end.

Definition equivL {A} : Equiv A := (=).

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

Global Instance const_proper `{R1 : relation A, R2 : relation B} (x : B) :
  Reflexive R2 → Proper (R1 ==> R2) (λ _, x).
Proof. intros ? y1 y2; reflexivity. Qed.

Global Instance id_inj {A} : Inj (=) (=) (@id A).
Proof. intros ??; auto. Qed.
Global Instance compose_inj {A B C} R1 R2 R3 (f : A → B) (g : B → C) :
  Inj R1 R2 f → Inj R2 R3 g → Inj R1 R3 (g ∘ f).
Proof. red; intuition. Qed.

Definition zip_with {A B C} (f : A → B → C) : list A → list B → list C :=
  fix go l1 l2 :=
  match l1, l2 with x1 :: l1, x2 :: l2 => f x1 x2 :: go l1 l2 | _ , _ => [] end.
Notation zip := (zip_with pair).

(** ** Booleans *)
(** The following coercion allows us to use Booleans as propositions. *)
Coercion Is_true : bool >-> Sortclass.
Global Hint Unfold Is_true : core.
Global Hint Immediate Is_true_eq_left : core.
Global Hint Resolve orb_prop_intro andb_prop_intro : core.
Notation "(&&)" := andb (only parsing).
Notation "(||)" := orb (only parsing).
Infix "&&*" := (zip_with (&&)) (at level 40).
Infix "||*" := (zip_with (||)) (at level 50).

Definition bool_le (β1 β2 : bool) : Prop := negb β1 || β2.
Infix "=.>" := bool_le (at level 70).
Infix "=.>*" := (Forall2 bool_le) (at level 70).

(** ** Unit *)
Global Instance unit_equiv : Equiv unit := λ _ _, True.
Global Instance unit_equivalence : Equivalence (≡@{unit}).
Proof. repeat split. Qed.
Global Instance unit_leibniz : LeibnizEquiv unit.
Proof. intros [] []; reflexivity. Qed.

(** ** Empty *)
Global Instance Empty_set_equiv : Equiv Empty_set := λ _ _, True.
Global Instance Empty_set_equivalence : Equivalence (≡@{Empty_set}).
Proof. repeat split. Qed.
Global Instance Empty_set_leibniz : LeibnizEquiv Empty_set.
Proof. intros [] []; reflexivity. Qed.

(** ** Products *)
Notation "( x ,.)" := (pair x) (only parsing) : stdpp_scope.
Notation "(., y )" := (λ x, (x,y)) (only parsing) : stdpp_scope.

Notation "p .1" := (fst p) (at level 2, left associativity, format "p .1").
Notation "p .2" := (snd p) (at level 2, left associativity, format "p .2").

Global Instance: Params (@pair) 2 := {}.
Global Instance: Params (@fst) 2 := {}.
Global Instance: Params (@snd) 2 := {}.

Global Instance: Params (@curry) 3 := {}.
Global Instance: Params (@uncurry) 3 := {}.

Definition uncurry3 {A B C D} (f : A → B → C → D) (p : A * B * C) : D :=
  let '(a,b,c) := p in f a b c.
Global Instance: Params (@uncurry3) 4 := {}.
Definition uncurry4 {A B C D E} (f : A → B → C → D → E) (p : A * B * C * D) : E :=
  let '(a,b,c,d) := p in f a b c d.
Global Instance: Params (@uncurry4) 5 := {}.

Definition curry3 {A B C D} (f : A * B * C → D) (a : A) (b : B) (c : C) : D :=
  f (a, b, c).
Global Instance: Params (@curry3) 4 := {}.
Definition curry4 {A B C D E} (f : A * B * C * D → E)
  (a : A) (b : B) (c : C) (d : D) : E := f (a, b, c, d).
Global Instance: Params (@curry4) 5 := {}.

Definition prod_map {A A' B B'} (f: A → A') (g: B → B') (p : A * B) : A' * B' :=
  (f (p.1), g (p.2)).
Global Arguments prod_map {_ _ _ _} _ _ !_ / : assert.

Definition prod_zip {A A' A'' B B' B''} (f : A → A' → A'') (g : B → B' → B'')
    (p : A * B) (q : A' * B') : A'' * B'' := (f (p.1) (q.1), g (p.2) (q.2)).
Global Arguments prod_zip {_ _ _ _ _ _} _ _ !_ !_ / : assert.

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

  Global Instance prod_relation_refl :
    Reflexive RA → Reflexive RB → Reflexive (prod_relation RA RB).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_sym :
    Symmetric RA → Symmetric RB → Symmetric (prod_relation RA RB).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_trans :
    Transitive RA → Transitive RB → Transitive (prod_relation RA RB).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_equiv :
    Equivalence RA → Equivalence RB → Equivalence (prod_relation RA RB).
  Proof. split; apply _. Qed.

  Global Instance pair_proper' : Proper (RA ==> RB ==> prod_relation RA RB) pair.
  Proof. firstorder eauto. Qed.
  Global Instance pair_inj' : Inj2 RA RB (prod_relation RA RB) pair.
  Proof. inversion_clear 1; eauto. Qed.
  Global Instance fst_proper' : Proper (prod_relation RA RB ==> RA) fst.
  Proof. firstorder eauto. Qed.
  Global Instance snd_proper' : Proper (prod_relation RA RB ==> RB) snd.
  Proof. firstorder eauto. Qed.

  Global Instance curry_proper' `{RC : relation C} :
    Proper ((prod_relation RA RB ==> RC) ==> RA ==> RB ==> RC) curry.
  Proof. firstorder eauto. Qed.
  Global Instance uncurry_proper' `{RC : relation C} :
    Proper ((RA ==> RB ==> RC) ==> prod_relation RA RB ==> RC) uncurry.
  Proof. intros f1 f2 Hf [x1 y1] [x2 y2] []; apply Hf; assumption. Qed.

  Global Instance curry3_proper' `{RC : relation C, RD : relation D} :
    Proper ((prod_relation (prod_relation RA RB) RC ==> RD) ==>
            RA ==> RB ==> RC ==> RD) curry3.
  Proof. firstorder eauto. Qed.
  Global Instance uncurry3_proper' `{RC : relation C, RD : relation D} :
    Proper ((RA ==> RB ==> RC ==> RD) ==>
            prod_relation (prod_relation RA RB) RC ==> RD) uncurry3.
  Proof. intros f1 f2 Hf [[??] ?] [[??] ?] [[??] ?]; apply Hf; assumption. Qed.

  Global Instance curry4_proper' `{RC : relation C, RD : relation D, RE : relation E} :
    Proper ((prod_relation (prod_relation (prod_relation RA RB) RC) RD ==> RE) ==>
            RA ==> RB ==> RC ==> RD ==> RE) curry4.
  Proof. firstorder eauto. Qed.
  Global Instance uncurry4_proper' `{RC : relation C, RD : relation D, RE : relation E} :
    Proper ((RA ==> RB ==> RC ==> RD ==> RE) ==>
            prod_relation (prod_relation (prod_relation RA RB) RC) RD ==> RE) uncurry4.
  Proof.
    intros f1 f2 Hf [[[??] ?] ?] [[[??] ?] ?] [[[??] ?] ?]; apply Hf; assumption.
  Qed.
Elpi myEnd.

(* Elpi add_instances Inj. *)
(* Elpi Print TC_check. *)

Global Instance prod_equiv `{Equiv A,Equiv B} : Equiv (A * B) :=
  prod_relation (≡) (≡).

(** Below we make [prod_equiv] type class opaque, so we first lift all
instances *)
Section prod_setoid.
  Context `{Equiv A, Equiv B}.

  Global Instance prod_equivalence :
    Equivalence (≡@{A}) → Equivalence (≡@{B}) → Equivalence (≡@{A * B}) := _.

  Global Instance pair_proper : Proper ((≡) ==> (≡) ==> (≡@{A*B})) pair := _.

  Elpi Accumulate TC_check lp:{{
    tc {{:gref Inj2}} {{Inj2 _ _ lp:R3 lp:F}} S :-
      R3 = app [global {coq.locate "equiv"} | _],
      Res = {{prod_relation _ _}},
      coq.unify-eq R3 Res ok,
      tc {{:gref Inj2}} {{Inj2 _ _ lp:Res lp:F}} S.
  }}.
  Elpi Typecheck TC_check.

  Elpi add_instances Inj2.
  Global Instance pair_equiv_inj : Inj2 (≡) (≡) (≡@{A*B}) pair := _.
  Global Instance fst_proper : Proper ((≡@{A*B}) ==> (≡)) fst := _.
  Global Instance snd_proper : Proper ((≡@{A*B}) ==> (≡)) snd := _.

  Global Instance curry_proper `{Equiv C} :
    Proper (((≡@{A*B}) ==> (≡@{C})) ==> (≡) ==> (≡) ==> (≡)) curry := _.
  Global Instance uncurry_proper `{Equiv C} :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡@{A*B}) ==> (≡@{C})) uncurry := _.

  Global Instance curry3_proper `{Equiv C, Equiv D} :
    Proper (((≡@{A*B*C}) ==> (≡@{D})) ==>
            (≡) ==> (≡) ==> (≡) ==> (≡)) curry3 := _.
  Global Instance uncurry3_proper `{Equiv C, Equiv D} :
    Proper (((≡) ==> (≡) ==> (≡) ==> (≡)) ==>
            (≡@{A*B*C}) ==> (≡@{D})) uncurry3 := _.

  Global Instance curry4_proper `{Equiv C, Equiv D, Equiv E} :
    Proper (((≡@{A*B*C*D}) ==> (≡@{E})) ==>
            (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) curry4 := _.
  Global Instance uncurry4_proper `{Equiv C, Equiv D, Equiv E} :
    Proper (((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) ==>
            (≡@{A*B*C*D}) ==> (≡@{E})) uncurry4 := _.
Elpi myEnd.

Typeclasses Opaque prod_equiv.

Global Instance prod_leibniz `{LeibnizEquiv A, LeibnizEquiv B} :
  LeibnizEquiv (A * B).
Proof. intros [??] [??] [??]; f_equal; apply leibniz_equiv; auto. Qed.

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
  Global Instance sum_relation_refl :
    Reflexive RA → Reflexive RB → Reflexive (sum_relation RA RB).
  Proof. intros ?? [?|?]; constructor; reflexivity. Qed.
  Global Instance sum_relation_sym :
    Symmetric RA → Symmetric RB → Symmetric (sum_relation RA RB).
  Proof. destruct 3; constructor; eauto. Qed.
  Global Instance sum_relation_trans :
    Transitive RA → Transitive RB → Transitive (sum_relation RA RB).
  Proof. destruct 3; inversion_clear 1; constructor; eauto. Qed.
  Global Instance sum_relation_equiv :
    Equivalence RA → Equivalence RB → Equivalence (sum_relation RA RB).
  Proof. split; apply _. Qed.
  Global Instance inl_proper' : Proper (RA ==> sum_relation RA RB) inl.
  Proof. constructor; auto. Qed.
  Global Instance inr_proper' : Proper (RB ==> sum_relation RA RB) inr.
  Proof. constructor; auto. Qed.
  Global Instance inl_inj' : Inj RA (sum_relation RA RB) inl.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance inr_inj' : Inj RB (sum_relation RA RB) inr.
  Proof. inversion_clear 1; auto. Qed.
Elpi myEnd.

Global Instance sum_equiv `{Equiv A, Equiv B} : Equiv (A + B) := sum_relation (≡) (≡).
Global Instance inl_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@inl A B) := _.
Global Instance inr_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@inr A B) := _.

(* Elpi added here *)
Elpi Accumulate TC_check lp:{{
  tc {{:gref Inj}} {{Inj lp:R1 (@equiv (sum _ _) (@sum_equiv _ _ _ _)) lp:S}} C :-
    tc {{:gref Inj}} {{Inj lp:R1 (sum_relation _ _) lp:S}} C.
}}.
Elpi Typecheck TC_check.

Global Instance inl_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inl A B) := _.
Global Instance inr_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inr A B) := _.
Typeclasses Opaque sum_equiv.

(** ** Sigma types *)
Global Arguments existT {_ _} _ _ : assert.
Global Arguments projT1 {_ _} _ : assert.
Global Arguments projT2 {_ _} _ : assert.

Global Arguments exist {_} _ _ _ : assert.
Global Arguments proj1_sig {_ _} _ : assert.
Global Arguments proj2_sig {_ _} _ : assert.
Notation "x ↾ p" := (exist _ x p) (at level 20) : stdpp_scope.
Notation "` x" := (proj1_sig x) (at level 10, format "` x") : stdpp_scope.

(* Elpi add_instances Inj ignoreInstances compose_inj. *)
Elpi Override TC TC_check Only Inj.

Elpi AddAllInstances compose_inj.

Definition f := Nat.add 0.
Global Instance h: Inj eq eq f. 
  unfold f. simpl. easy.
Qed.

Elpi Query TC_check lp:{{
  std.forall [{{:gref compose_inj}}, {{:gref h}}] 
  (Inst\ sigma Ty C\
  coq.env.typeof Inst Ty,
  compile Ty (global Inst) [] [] C,
  add-tc-db (after "complexHook") C).
}}.
