From elpi.apps Require Import tc.
Elpi Override TC TC_solver All.

(** This file collects type class interfaces, notations, and general theorems
that are used throughout the whole development. Most importantly it contains
abstract interfaces for ordered structures, sets, and various other data
structures. *)

(* We want to ensure that [le] and [lt] refer to operations on [nat].
These two functions being defined both in [Coq.Bool] and in [Coq.Peano],
we must export [Coq.Peano] later than any export of [Coq.Bool]. *)
(* We also want to ensure that notations from [Coq.Utf8] take precedence
over the ones of [Coq.Peano] (see Coq PR#12950), so we import [Utf8] last. *)
From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.
From Coq Require Import Permutation.
Export ListNotations.
From Coq.Program Require Export Basics Syntax.

Elpi AddAllClasses.
Elpi AddAllInstances.

(** This notation is necessary to prevent [length] from being printed
as [strings.length] if strings.v is imported and later base.v. See
also strings.v and
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/144 and
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/129. *)
Notation length := Datatypes.length.

(** * Enable implicit generalization. *)
(** This option enables implicit generalization in arguments of the form
   [`{...}] (i.e., anonymous arguments).  Unfortunately, it also enables
   implicit generalization in [Instance].  We think that the fact that both
   behaviors are coupled together is a [bug in
   Coq](https://github.com/coq/coq/issues/6030). *)
Global Generalizable All Variables.

(** * Tweak program *)
(** 1. Since we only use Program to solve logical side-conditions, they should
always be made Opaque, otherwise we end up with performance problems due to
Coq blindly unfolding them.

Note that in most cases we use [Next Obligation. (* ... *) Qed.], for which
this option does not matter. However, sometimes we write things like
[Solve Obligations with naive_solver (* ... *)], and then the obligations
should surely be opaque. *)
Global Unset Transparent Obligations.

(** 2. Do not let Program automatically simplify obligations. The default
obligation tactic is [Tactics.program_simpl], which, among other things,
introduces all variables and gives them fresh names. As such, it becomes
impossible to refer to hypotheses in a robust way. *)
Global Obligation Tactic := idtac.

(** 3. Hide obligations and unsealing lemmas from the results of the [Search]
commands. *)
Add Search Blacklist "_obligation_".
Add Search Blacklist "_unseal".

(** * Sealing off definitions *)
#[projections(primitive=yes)]
Record seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
Global Arguments unseal {_ _} _ : assert.
Global Arguments seal_eq {_ _} _ : assert.

(** * Solving type class instances *)
(** The tactic [tc_solve] is used to solve type class goals by invoking type
class search. It is similar to [apply _], but it is more robust since it does
not affect unrelated goals/evars due to https://github.com/coq/coq/issues/6583.

The tactic [tc_solve] is particularly useful when building custom tactics that
need tight control over when type class search is invoked. In Iris, many of the
proof mode tactics make use of [notypeclasses refine] and use [tc_solve] to
manually invoke type class search.

Note that [typeclasses eauto] is multi-success. That means, whenever subsequent
tactics fail, it will backtrack to [typeclasses eauto] to try the next type
class instance. This is almost always undesired and can lead to poor performance
and horrible error messages. Hence, we wrap it in a [once]. *)
Ltac tc_solve :=
  solve [once (typeclasses eauto)].

(** * Non-backtracking type classes *)
(** The type class [TCNoBackTrack P] can be used to establish [P] without ever
backtracking on the instance of [P] that has been found. Backtracking may
normally happen when [P] contains evars that could be instanciated in different
ways depending on which instance is picked, and type class search somewhere else
depends on this evar.

The proper way of handling this would be by setting Coq's option
`Typeclasses Unique Instances`. However, this option seems to be broken, see Coq
issue #6714.

See https://gitlab.mpi-sws.org/FP/iris-coq/merge_requests/112 for a rationale
of this type class. *)
Class TCNoBackTrack (P : Prop) := TCNoBackTrack_intro { tc_no_backtrack : P }.
Global Hint Extern 0 (TCNoBackTrack _) =>
  notypeclasses refine (TCNoBackTrack_intro _ _); tc_solve : typeclass_instances.

(* A conditional at the type class level. Note that [TCIf P Q R] is not the same
as [TCOr (TCAnd P Q) R]: the latter will backtrack to [R] if it fails to
establish [Q], i.e. does not have the behavior of a conditional. Furthermore,
note that [TCOr (TCAnd P Q) (TCAnd (TCNot P) R)] would not work; we generally
would not be able to prove the negation of [P]. *)
Inductive TCIf (P Q R : Prop) : Prop :=
  | TCIf_true : P → Q → TCIf P Q R
  | TCIf_false : R → TCIf P Q R.
Existing Class TCIf.

Global Hint Extern 0 (TCIf _ _ _) =>
  first [notypeclasses refine (TCIf_true _ _ _ _ _); [tc_solve|]
        |notypeclasses refine (TCIf_false _ _ _ _)] : typeclass_instances.

(** * Typeclass opaque definitions *)
(** The constant [tc_opaque] is used to make definitions opaque for just type
class search. Note that [simpl] is set up to always unfold [tc_opaque]. *)
Definition tc_opaque {A} (x : A) : A := x.
Global Typeclasses Opaque tc_opaque.
Global Arguments tc_opaque {_} _ /.

(** Below we define type class versions of the common logical operators. It is
important to note that we duplicate the definitions, and do not declare the
existing logical operators as type classes. That is, we do not say:

  Existing Class or.
  Existing Class and.

If we could define the existing logical operators as classes, there is no way
of disambiguating whether a premise of a lemma should be solved by type class
resolution or not.

These classes are useful for two purposes: writing complicated type class
premises in a more concise way, and for efficiency. For example, using the [Or]
class, instead of defining two instances [P → Q1 → R] and [P → Q2 → R] we could
have one instance [P → Or Q1 Q2 → R]. When we declare the instance that way, we
avoid the need to derive [P] twice. *)
Inductive TCOr (P1 P2 : Prop) : Prop :=
  | TCOr_l : P1 → TCOr P1 P2
  | TCOr_r : P2 → TCOr P1 P2.
Existing Class TCOr.
Global Existing Instance TCOr_l | 9.
Global Existing Instance TCOr_r | 10.
Global Hint Mode TCOr ! ! : typeclass_instances.

Inductive TCAnd (P1 P2 : Prop) : Prop := TCAnd_intro : P1 → P2 → TCAnd P1 P2.
Existing Class TCAnd.
Global Existing Instance TCAnd_intro.
Global Hint Mode TCAnd ! ! : typeclass_instances.

Inductive TCTrue : Prop := TCTrue_intro : TCTrue.
Existing Class TCTrue.
Global Existing Instance TCTrue_intro.

(** The class [TCFalse] is not stricly necessary as one could also use
[False]. However, users might expect that TCFalse exists and if it
does not, it can cause hard to diagnose bugs due to automatic
generalization. *)
Inductive TCFalse : Prop :=.
Existing Class TCFalse.

(** The class [TCUnless] can be used to check that search for [P]
fails. This is useful as a guard for certain instances together with
classes like [TCFastDone] (see [tactics.v]) to prevent infinite loops
(e.g. when saturating the context). *)
Notation TCUnless P := (TCIf P TCFalse TCTrue).

Inductive TCForall {A} (P : A → Prop) : list A → Prop :=
  | TCForall_nil : TCForall P []
  | TCForall_cons x xs : P x → TCForall P xs → TCForall P (x :: xs).
Existing Class TCForall.
Global Existing Instance TCForall_nil.
Global Existing Instance TCForall_cons.
Global Hint Mode TCForall ! ! ! : typeclass_instances.

(** The class [TCForall2 P l k] is commonly used to transform an input list [l]
into an output list [k], or the converse. Therefore there are two modes, either
[l] input and [k] output, or [k] input and [l] input. *)
Inductive TCForall2 {A B} (P : A → B → Prop) : list A → list B → Prop :=
  | TCForall2_nil : TCForall2 P [] []
  | TCForall2_cons x y xs ys :
     P x y → TCForall2 P xs ys → TCForall2 P (x :: xs) (y :: ys).
Existing Class TCForall2.
Global Existing Instance TCForall2_nil.
Global Existing Instance TCForall2_cons.
Global Hint Mode TCForall2 ! ! ! ! - : typeclass_instances.
Global Hint Mode TCForall2 ! ! ! - ! : typeclass_instances.

Inductive TCExists {A} (P : A → Prop) : list A → Prop :=
  | TCExists_cons_hd x l : P x → TCExists P (x :: l)
  | TCExists_cons_tl x l: TCExists P l → TCExists P (x :: l).
Existing Class TCExists.
Global Existing Instance TCExists_cons_hd | 10.
Global Existing Instance TCExists_cons_tl | 20.
Global Hint Mode TCExists ! ! ! : typeclass_instances.

Inductive TCElemOf {A} (x : A) : list A → Prop :=
  | TCElemOf_here xs : TCElemOf x (x :: xs)
  | TCElemOf_further y xs : TCElemOf x xs → TCElemOf x (y :: xs).
Existing Class TCElemOf.
Global Existing Instance TCElemOf_here.
Global Existing Instance TCElemOf_further.
Global Hint Mode TCElemOf ! ! ! : typeclass_instances.

(** The intended use of [TCEq x y] is to use [x] as input and [y] as output, but
this is not enforced. We use output mode [-] (instead of [!]) for [x] to ensure
that type class search succeed on goals like [TCEq (if ? then e1 else e2) ?y],
see https://gitlab.mpi-sws.org/iris/iris/merge_requests/391 for a use case.
Mode [-] is harmless, the only instance of [TCEq] is [TCEq_refl] below, so we
cannot create loops. *)
Inductive TCEq {A} (x : A) : A → Prop := TCEq_refl : TCEq x x.
Existing Class TCEq.
Global Existing Instance TCEq_refl.
Global Hint Mode TCEq ! - - : typeclass_instances.

Lemma TCEq_eq {A} (x1 x2 : A) : TCEq x1 x2 ↔ x1 = x2.
Proof. split; destruct 1; reflexivity. Qed.

(** The [TCSimpl x y] type class is similar to [TCEq] but performs [simpl]
before proving the goal by reflexivity. Similar to [TCEq], the argument [x]
is the input and [y] the output. When solving [TCEq x y], the argument [x]
should be a concrete term and [y] an evar for the [simpl]ed result. *)
Class TCSimpl {A} (x x' : A) := TCSimpl_TCEq : TCEq x x'.
Global Hint Extern 0 (TCSimpl _ _) =>
  (* Since the second argument should be an evar, we can call [simpl] on the
  whole goal. *)
  simpl; notypeclasses refine (TCEq_refl _) : typeclass_instances.
Global Hint Mode TCSimpl ! - - : typeclass_instances.

Lemma TCSimpl_eq {A} (x1 x2 : A) : TCSimpl x1 x2 ↔ x1 = x2.
Proof. apply TCEq_eq. Qed.

Inductive TCDiag {A} (C : A → Prop) : A → A → Prop :=
  | TCDiag_diag x : C x → TCDiag C x x.
Existing Class TCDiag.
Global Existing Instance TCDiag_diag.
Global Hint Mode TCDiag ! ! ! - : typeclass_instances.
Global Hint Mode TCDiag ! ! - ! : typeclass_instances.

(** Given a proposition [P] that is a type class, [tc_to_bool P] will return
[true] iff there is an instance of [P]. It is often useful in Ltac programming,
where one can do [lazymatch tc_to_bool P with true => .. | false => .. end]. *)
Definition tc_to_bool (P : Prop)
  {p : bool} `{TCIf P (TCEq p true) (TCEq p false)} : bool := p.

(** Throughout this development we use [stdpp_scope] for all general purpose
notations that do not belong to a more specific scope. *)
Declare Scope stdpp_scope.
Delimit Scope stdpp_scope with stdpp.
Global Open Scope stdpp_scope.

(** Change [True] and [False] into notations in order to enable overloading.
We will use this to give [True] and [False] a different interpretation for
embedded logics. *)
Notation "'True'" := True (format "True") : type_scope.
Notation "'False'" := False (format "False") : type_scope.

(** Change [forall] into a notation in order to enable overloading. *)
Notation "'forall' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   only parsing) : type_scope.


(** * Equality *)
(** Introduce some Haskell style like notations. *)
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

(** ** Setoid equality *)
(** We define an operational type class for setoid equality, i.e., the
"canonical" equivalence for a type. The typeclass is tied to the \equiv
symbol. This is based on (Spitters/van der Weegen, 2011). *)
Class Equiv A := equiv: relation A.
Global Hint Mode Equiv ! : typeclass_instances.

(** We instruct setoid rewriting to infer [equiv] as a relation on
type [A] when needed. This allows setoid_rewrite to solve constraints
of shape [Proper (eq ==> ?R) f] using [Proper (eq ==> (equiv (A:=A))) f]
when an equivalence relation is available on type [A]. We put this instance
at level 150 so it does not take precedence over Coq's stdlib instances,
favoring inference of [eq] (all Coq functions are automatically morphisms
for [eq]). We have [eq] (at 100) < [≡] (at 150) < [⊑] (at 200). *)
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

(** The type class [LeibnizEquiv] collects setoid equalities that coincide
with Leibniz equality. We provide the tactic [fold_leibniz] to transform such
setoid equalities into Leibniz equalities, and [unfold_leibniz] for the
reverse.

Various std++ tactics assume that this class is only instantiated if [≡]
is an equivalence relation. *)
Class LeibnizEquiv A `{Equiv A} :=
  leibniz_equiv (x y : A) : x ≡ y → x = y.
Global Hint Mode LeibnizEquiv ! ! : typeclass_instances.

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

(** A [Params f n] instance forces the setoid rewriting mechanism not to
rewrite in the first [n] arguments of the function [f]. We will declare such
instances for all operational type classes in this development. *)
Global Instance: Params (@equiv) 2 := {}.

(** The following instance forces [setoid_replace] to use setoid equality
(for types that have an [Equiv] instance) rather than the standard Leibniz
equality. *)
Global Instance equiv_default_relation `{Equiv A} :
  DefaultRelation (≡@{A}) | 3 := {}.
Global Hint Extern 0 (_ ≡ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡ _) => symmetry; assumption : core.


(** * Type classes *)
(** ** Decidable propositions *)
(** This type class by (Spitters/van der Weegen, 2011) collects decidable
propositions. *)
Class Decision (P : Prop) := decide : {P} + {¬P}.
Global Hint Mode Decision ! : typeclass_instances.
Global Arguments decide _ {_} : simpl never, assert.

(** Although [RelDecision R] is just [∀ x y, Decision (R x y)], we make this
an explicit class instead of a notation for two reasons:

- It allows us to control [Hint Mode] more precisely. In particular, if it were
  defined as a notation, the above [Hint Mode] for [Decision] would not prevent
  diverging instance search when looking for [RelDecision (@eq ?A)], which would
  result in it looking for [Decision (@eq ?A x y)], i.e. an instance where the
  head position of [Decision] is not en evar.
- We use it to avoid inefficient computation due to eager evaluation of
  propositions by [vm_compute]. This inefficiency arises for example if
  [(x = y) := (f x = f y)]. Since [decide (x = y)] evaluates to
  [decide (f x = f y)], this would then lead to evaluation of [f x] and [f y].
  Using the [RelDecision], the [f] is hidden under a lambda, which prevents
  unnecessary evaluation. *)
Class RelDecision {A B} (R : A → B → Prop) :=
  decide_rel x y :> Decision (R x y).
Global Hint Mode RelDecision ! ! ! : typeclass_instances.
Global Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.
Notation EqDecision A := (RelDecision (=@{A})).

(** ** Inhabited types *)
(** This type class collects types that are inhabited. *)
Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Global Hint Mode Inhabited ! : typeclass_instances.
Global Arguments populate {_} _ : assert.

(** ** Proof irrelevant types *)
(** This type class collects types that are proof irrelevant. That means, all
elements of the type are equal. We use this notion only used for propositions,
but by universe polymorphism we can generalize it. *)
Class ProofIrrel (A : Type) : Prop := proof_irrel (x y : A) : x = y.
Global Hint Mode ProofIrrel ! : typeclass_instances.

(** ** Common properties *)
(** These operational type classes allow us to refer to common mathematical
properties in a generic way. For example, for injectivity of [(k ++.)] it
allows us to write [inj (k ++.)] instead of [app_inv_head k]. *)
Class Inj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop :=
  inj x y : S (f x) (f y) → R x y.
Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.
Class Cancel {A B} (S : relation B) (f : A → B) (g : B → A) : Prop :=
  cancel x : S (f (g x)) x.
Class Surj {A B} (R : relation B) (f : A → B) :=
  surj y : ∃ x, R (f x) y.
Class IdemP {A} (R : relation A) (f : A → A → A) : Prop :=
  idemp x : R (f x x) x.
Class Comm {A B} (R : relation A) (f : B → B → A) : Prop :=
  comm x y : R (f x y) (f y x).
Class LeftId {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  left_id x : R (f i x) x.
Class RightId {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  right_id x : R (f x i) x.
Class Assoc {A} (R : relation A) (f : A → A → A) : Prop :=
  assoc x y z : R (f x (f y z)) (f (f x y) z).
Class LeftAbsorb {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  left_absorb x : R (f i x) i.
Class RightAbsorb {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  right_absorb x : R (f x i) i.
Class AntiSymm {A} (R S : relation A) : Prop :=
  anti_symm x y : S x y → S y x → R x y.
Class Total {A} (R : relation A) := total x y : R x y ∨ R y x.
Class Trichotomy {A} (R : relation A) :=
  trichotomy x y : R x y ∨ x = y ∨ R y x.
Class TrichotomyT {A} (R : relation A) :=
  trichotomyT x y : {R x y} + {x = y} + {R y x}.

Notation Involutive R f := (Cancel R f f).
Lemma involutive {A} {R : relation A} (f : A → A) `{Involutive R f} x :
  R (f (f x)) x.
Proof. auto. Qed.

Global Arguments irreflexivity {_} _ {_} _ _ : assert.
Global Arguments inj {_ _ _ _} _ {_} _ _ _ : assert.
Global Arguments inj2 {_ _ _ _ _ _} _ {_} _ _ _ _ _: assert.
Global Arguments cancel {_ _ _} _ _ {_} _ : assert.
Global Arguments surj {_ _ _} _ {_} _ : assert.
Global Arguments idemp {_ _} _ {_} _ : assert.
Global Arguments comm {_ _ _} _ {_} _ _ : assert.
Global Arguments left_id {_ _} _ _ {_} _ : assert.
Global Arguments right_id {_ _} _ _ {_} _ : assert.
Global Arguments assoc {_ _} _ {_} _ _ _ : assert.
Global Arguments left_absorb {_ _} _ _ {_} _ : assert.
Global Arguments right_absorb {_ _} _ _ {_} _ : assert.
Global Arguments anti_symm {_ _} _ {_} _ _ _ _ : assert.
Global Arguments total {_} _ {_} _ _ : assert.
Global Arguments trichotomy {_} _ {_} _ _ : assert.
Global Arguments trichotomyT {_} _ {_} _ _ : assert.

Lemma not_symmetry `{R : relation A, !Symmetric R} x y : ¬R x y → ¬R y x.
Proof. intuition. Qed.
Lemma symmetry_iff `(R : relation A) `{!Symmetric R} x y : R x y ↔ R y x.
Proof. intuition. Qed.

Lemma not_inj `{Inj A B R R' f} x y : ¬R x y → ¬R' (f x) (f y).
Proof. intuition. Qed.
Lemma not_inj2_1 `{Inj2 A B C R R' R'' f} x1 x2 y1 y2 :
  ¬R x1 x2 → ¬R'' (f x1 y1) (f x2 y2).
Proof. intros HR HR''. destruct (inj2 f x1 y1 x2 y2); auto. Qed.
Lemma not_inj2_2 `{Inj2 A B C R R' R'' f} x1 x2 y1 y2 :
  ¬R' y1 y2 → ¬R'' (f x1 y1) (f x2 y2).
Proof. intros HR' HR''. destruct (inj2 f x1 y1 x2 y2); auto. Qed.

Lemma inj_iff {A B} {R : relation A} {S : relation B} (f : A → B)
  `{!Inj R S f} `{!Proper (R ==> S) f} x y : S (f x) (f y) ↔ R x y.
Proof. firstorder. Qed.
Global Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 f} y : Inj R1 R3 (λ x, f x y).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.
Global Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 f} x : Inj R2 R3 (f x).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.
Elpi Override TC - ProperProxy.

Lemma cancel_inj `{Cancel A B R1 f g, !Equivalence R1, !Proper (R2 ==> R1) f} :
  Inj R1 R2 g.
Proof.
  intros x y E. rewrite <-(cancel f g x), <-(cancel f g y), E. reflexivity.
Qed.
Lemma cancel_surj `{Cancel A B R1 f g} : Surj R1 f.
Proof. intros y. exists (g y). auto. Qed.

(** The following lemmas are specific versions of the projections of the above
type classes for Leibniz equality. These lemmas allow us to enforce Coq not to
use the setoid rewriting mechanism. *)
Lemma idemp_L {A} f `{!@IdemP A (=) f} x : f x x = x.
Proof. auto. Qed.
Lemma comm_L {A B} f `{!@Comm A B (=) f} x y : f x y = f y x.
Proof. auto. Qed.
Lemma left_id_L {A} i f `{!@LeftId A (=) i f} x : f i x = x.
Proof. auto. Qed.
Lemma right_id_L {A} i f `{!@RightId A (=) i f} x : f x i = x.
Proof. auto. Qed.
Lemma assoc_L {A} f `{!@Assoc A (=) f} x y z : f x (f y z) = f (f x y) z.
Proof. auto. Qed.
Lemma left_absorb_L {A} i f `{!@LeftAbsorb A (=) i f} x : f i x = i.
Proof. auto. Qed.
Lemma right_absorb_L {A} i f `{!@RightAbsorb A (=) i f} x : f x i = i.
Proof. auto. Qed.

(** ** Generic orders *)
(** The classes [PreOrder], [PartialOrder], and [TotalOrder] use an arbitrary
relation [R] instead of [⊆] to support multiple orders on the same type. *)
Definition strict {A} (R : relation A) : relation A := λ X Y, R X Y ∧ ¬R Y X.
Global Instance: Params (@strict) 2 := {}.

Class PartialOrder {A} (R : relation A) : Prop := {
  partial_order_pre :> PreOrder R;
  partial_order_anti_symm :> AntiSymm (=) R
}.
Global Hint Mode PartialOrder ! ! : typeclass_instances.

Class TotalOrder {A} (R : relation A) : Prop := {
  total_order_partial :> PartialOrder R;
  total_order_trichotomy :> Trichotomy (strict R)
}.
Global Hint Mode TotalOrder ! ! : typeclass_instances.

(** * Logic *)
Global Instance prop_inhabited : Inhabited Prop := populate True.

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

Lemma or_l P Q : ¬Q → P ∨ Q ↔ P.
Proof. tauto. Qed.
Lemma or_r P Q : ¬P → P ∨ Q ↔ Q.
Proof. tauto. Qed.
Lemma and_wlog_l (P Q : Prop) : (Q → P) → Q → (P ∧ Q).
Proof. tauto. Qed.
Lemma and_wlog_r (P Q : Prop) : P → (P → Q) → (P ∧ Q).
Proof. tauto. Qed.
Lemma impl_transitive (P Q R : Prop) : (P → Q) → (Q → R) → (P → R).
Proof. tauto. Qed.
Lemma forall_proper {A} (P Q : A → Prop) :
  (∀ x, P x ↔ Q x) → (∀ x, P x) ↔ (∀ x, Q x).
Proof. firstorder. Qed.
Lemma exist_proper {A} (P Q : A → Prop) :
  (∀ x, P x ↔ Q x) → (∃ x, P x) ↔ (∃ x, Q x).
Proof. firstorder. Qed.

Global Instance eq_comm {A} : Comm (↔) (=@{A}).
Proof. red; intuition. Qed.
Global Instance flip_eq_comm {A} : Comm (↔) (λ x y, y =@{A} x).
Proof. red; intuition. Qed.
Global Instance iff_comm : Comm (↔) (↔).
Proof. red; intuition. Qed.
Global Instance and_comm : Comm (↔) (∧).
Proof. red; intuition. Qed.
Global Instance and_assoc : Assoc (↔) (∧).
Proof. red; intuition. Qed.
Global Instance and_idemp : IdemP (↔) (∧).
Proof. red; intuition. Qed.
Global Instance or_comm : Comm (↔) (∨).
Proof. red; intuition. Qed.
Global Instance or_assoc : Assoc (↔) (∨).
Proof. red; intuition. Qed.
Global Instance or_idemp : IdemP (↔) (∨).
Proof. red; intuition. Qed.
Global Instance True_and : LeftId (↔) True (∧).
Proof. red; intuition. Qed.
Global Instance and_True : RightId (↔) True (∧).
Proof. red; intuition. Qed.
Global Instance False_and : LeftAbsorb (↔) False (∧).
Proof. red; intuition. Qed.
Global Instance and_False : RightAbsorb (↔) False (∧).
Proof. red; intuition. Qed.
Global Instance False_or : LeftId (↔) False (∨).
Proof. red; intuition. Qed.
Global Instance or_False : RightId (↔) False (∨).
Proof. red; intuition. Qed.
Global Instance True_or : LeftAbsorb (↔) True (∨).
Proof. red; intuition. Qed.
Global Instance or_True : RightAbsorb (↔) True (∨).
Proof. red; intuition. Qed.
Global Instance True_impl : LeftId (↔) True impl.
Proof. unfold impl. red; intuition. Qed.
Global Instance impl_True : RightAbsorb (↔) True impl.
Proof. unfold impl. red; intuition. Qed.


(** * Common data types *)
(** ** Functions *)
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

Global Instance impl_inhabited {A} `{Inhabited B} : Inhabited (A → B) :=
  populate (λ _, inhabitant).

(** Ensure that [simpl] unfolds [id], [compose], and [flip] when fully
applied. *)
Global Arguments id _ _ / : assert.
Global Arguments compose _ _ _ _ _ _ / : assert.
Global Arguments flip _ _ _ _ _ _ / : assert.
Global Arguments const _ _ _ _ / : assert.
Global Typeclasses Transparent id compose flip const.

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

Global Instance id_surj {A} : Surj (=) (@id A).
Proof. intros y; exists y; reflexivity. Qed.
Global Instance compose_surj {A B C} R (f : A → B) (g : B → C) :
  Surj (=) f → Surj R g → Surj R (g ∘ f).
Proof.
  intros ?? x. unfold compose. destruct (surj g x) as [y ?].
  destruct (surj f y) as [z ?]. exists z. congruence.
Qed.

Global Instance const2_comm {A B} (x : B) : Comm (=) (λ _ _ : A, x).
Proof. intros ?; reflexivity. Qed.
Global Instance const2_assoc {A} (x : A) : Assoc (=) (λ _ _ : A, x).
Proof. intros ???; reflexivity. Qed.
Global Instance id1_assoc {A} : Assoc (=) (λ x _ : A, x).
Proof. intros ???; reflexivity. Qed.
Global Instance id2_assoc {A} : Assoc (=) (λ _ x : A, x).
Proof. intros ???; reflexivity. Qed.
Global Instance id1_idemp {A} : IdemP (=) (λ x _ : A, x).
Proof. intros ?; reflexivity. Qed.
Global Instance id2_idemp {A} : IdemP (=) (λ _ x : A, x).
Proof. intros ?; reflexivity. Qed.

(** ** Lists *)
Global Instance list_inhabited {A} : Inhabited (list A) := populate [].

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

Global Instance bool_inhabated : Inhabited bool := populate true.

Definition bool_le (β1 β2 : bool) : Prop := negb β1 || β2.
Infix "=.>" := bool_le (at level 70).
Infix "=.>*" := (Forall2 bool_le) (at level 70).
Global Instance: PartialOrder bool_le.
Proof. repeat split; repeat intros [|]; compute; tauto. Qed.

Lemma andb_True b1 b2 : b1 && b2 ↔ b1 ∧ b2.
Proof. destruct b1, b2; simpl; tauto. Qed.
Lemma orb_True b1 b2 : b1 || b2 ↔ b1 ∨ b2.
Proof. destruct b1, b2; simpl; tauto. Qed.
Lemma negb_True b : negb b ↔ ¬b.
Proof. destruct b; simpl; tauto. Qed.
Lemma Is_true_true (b : bool) : b ↔ b = true.
Proof. now destruct b. Qed.
Lemma Is_true_true_1 (b : bool) : b → b = true.
Proof. apply Is_true_true. Qed.
Lemma Is_true_true_2 (b : bool) : b = true → b.
Proof. apply Is_true_true. Qed.
Lemma Is_true_false (b : bool) : ¬ b ↔ b = false.
Proof. now destruct b; simpl. Qed.
Lemma Is_true_false_1 (b : bool) : ¬b → b = false.
Proof. apply Is_true_false. Qed.
Lemma Is_true_false_2 (b : bool) : b = false → ¬b.
Proof. apply Is_true_false. Qed.

(** ** Unit *)
Global Instance unit_equiv : Equiv unit := λ _ _, True.
Global Instance unit_equivalence : Equivalence (≡@{unit}).
Proof. repeat split. Qed.
Global Instance unit_leibniz : LeibnizEquiv unit.
Proof. intros [] []; reflexivity. Qed.
Global Instance unit_inhabited: Inhabited unit := populate ().

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
Global Instance: Params (@prod_map) 4 := {}.
Global Arguments prod_map {_ _ _ _} _ _ !_ / : assert.

Definition prod_zip {A A' A'' B B' B''} (f : A → A' → A'') (g : B → B' → B'')
    (p : A * B) (q : A' * B') : A'' * B'' := (f (p.1) (q.1), g (p.2) (q.2)).
Global Instance: Params (@prod_zip) 6 := {}.
Global Arguments prod_zip {_ _ _ _ _ _} _ _ !_ !_ / : assert.

Definition prod_swap {A B} (p : A * B) : B * A := (p.2, p.1).
Global Arguments prod_swap {_ _} !_ /.
Global Instance: Params (@prod_swap) 2 := {}.

Global Instance prod_inhabited {A B} (iA : Inhabited A)
    (iB : Inhabited B) : Inhabited (A * B) :=
  match iA, iB with populate x, populate y => populate (x,y) end.

(** Note that we need eta for products for the [uncurry_curry] lemmas to hold
in non-applied form ([uncurry (curry f) = f]). *)
Lemma curry_uncurry {A B C} (f : A → B → C) : curry (uncurry f) = f.
Proof. reflexivity. Qed.
Lemma uncurry_curry {A B C} (f : A * B → C) p : uncurry (curry f) p = f p.
Proof. destruct p; reflexivity. Qed.
Lemma curry3_uncurry3 {A B C D} (f : A → B → C → D) : curry3 (uncurry3 f) = f.
Proof. reflexivity. Qed.
Lemma uncurry3_curry3 {A B C D} (f : A * B * C → D) p :
  uncurry3 (curry3 f) p = f p.
Proof. destruct p as [[??] ?]; reflexivity. Qed.
Lemma curry4_uncurry4 {A B C D E} (f : A → B → C → D → E) :
  curry4 (uncurry4 f) = f.
Proof. reflexivity. Qed.
Lemma uncurry4_curry4 {A B C D E} (f : A * B * C * D → E) p :
  uncurry4 (curry4 f) p = f p.
Proof. destruct p as [[[??] ?] ?]; reflexivity. Qed.

(** [pair_eq] as a name is more consistent with our usual naming. *)
Lemma pair_eq {A B} (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) ↔ a1 = a2 ∧ b1 = b2.
Proof. apply pair_equal_spec. Qed.

Global Instance pair_inj {A B} : Inj2 (=) (=) (=) (@pair A B).
Proof. injection 1; auto. Qed.
Global Instance prod_map_inj {A A' B B'} (f : A → A') (g : B → B') :
  Inj (=) (=) f → Inj (=) (=) g → Inj (=) (=) (prod_map f g).
Proof.
  intros ?? [??] [??] ?; simpl in *; f_equal;
    [apply (inj f)|apply (inj g)]; congruence.
Qed.

Elpi Override TC - ProperProxy Proper.

Global Instance prod_swap_cancel {A B} :
  Cancel (=) (@prod_swap A B) (@prod_swap B A).
Proof. intros [??]; reflexivity. Qed.
Global Instance prod_swap_inj {A B} : Inj (=) (=) (@prod_swap A B).
Proof. apply cancel_inj. Qed.
Global Instance prod_swap_surj {A B} : Surj (=) (@prod_swap A B).
Proof. apply cancel_surj. Qed.

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

  Global Instance prod_swap_proper' :
    Proper (prod_relation RA RB ==> prod_relation RB RA) prod_swap.
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
End prod_relation.

Global Instance prod_equiv `{Equiv A,Equiv B} : Equiv (A * B) :=
  prod_relation (≡) (≡).

(** Below we make [prod_equiv] type class opaque, so we first lift all
instances *)
Section prod_setoid.
  Context `{Equiv A, Equiv B}.
  Elpi Accumulate TC_solver lp:{{
    shorten tc-Coq.Classes.RelationClasses.{tc-Equivalence}.
    :after "lastHook"
    tc-Equivalence A RA R :-
      RA = {{@equiv _ (@prod_equiv _ _ _ _)}},
      RA' = {{@prod_relation _ _ _ _}},
      coq.unify-eq RA RA' ok,
      % coq.say A RA,
      tc-Equivalence A RA' R.
  }}.
  (* Elpi Typecheck TC_solver. *)

  Global Instance prod_equivalence@{i} (C D: Type@{i}) `{Equiv C, Equiv D}:
    @Equivalence C (≡@{C}) → @Equivalence D (≡@{D}) → @Equivalence (C * D) (≡@{C * D}) := _.

  Elpi Accumulate TC_solver lp:{{
    
    pred remove_equiv_prod_equiv i:term, o:term.
    remove_equiv_prod_equiv T1 T3 :-
      T1 = {{@equiv _ (@prod_equiv _ _ _ _)}}, !,
      T2 = {{@prod_relation lp:F lp:G lp:A lp:B}},
      coq.unify-eq T1 T2 ok, 
      remove_equiv_prod_equiv A X,
      remove_equiv_prod_equiv B Y,
      {{@prod_relation lp:F lp:G lp:X lp:Y}} = T3.
    remove_equiv_prod_equiv (app L1) (app L2) :- !,
      std.map L1 remove_equiv_prod_equiv L2.
    remove_equiv_prod_equiv A A.

    shorten tc-Coq.Classes.Morphisms.{tc-Proper}.
    
    :after "lastHook" 
    tc-Proper A B C R :-
      B = {{ @respectful _ _ _ _ }},
      remove_equiv_prod_equiv B B1,
      tc-Proper A B1 C R.

    tc-Proper A {{@respectful lp:K1 lp:K2 lp:B1 (@respectful lp:K3 lp:K4 lp:B2 lp:B3)}} C S :-
      C1 = {{ @equiv _ _ }},
      C2 = {{ @equiv _ _ }},
      C3 = {{ @prod_relation _ _ _ _ }},
      coq.unify-eq B1 C1 ok,
      coq.unify-eq B2 C2 ok,
      coq.unify-eq B3 C3 ok,
      tc-Proper A {{@respectful lp:K1 lp:K2 lp:C1 (@respectful lp:K3 lp:K4 lp:C2 lp:C3)}} C S.
   
  }}.
  Elpi Typecheck TC_solver.

  Global Instance pair_proper : Proper ((≡) ==> (≡) ==> (≡@{A*B})) pair := _.

  Elpi Accumulate TC_solver lp:{{
    shorten tc-elpi.apps.tc.tests.bigTest.{tc-Inj2}.
    % shorten tc-bigTest.{tc-Inj2}.
    :after "lastHook" 
    tc-Inj2 A B C RA RB RC F S :-
      RC = app [global {coq.locate "equiv"} | _],
      remove_equiv_prod_equiv RC RC',
      tc-Inj2 A B C RA RB RC' F S.
  }}.
  Elpi Typecheck TC_solver.

  Global Instance pair_equiv_inj : Inj2 (≡) (≡) (≡@{A*B}) pair := _.
  Global Instance fst_proper : Proper ((≡@{A*B}) ==> (≡)) fst := _.
  Global Instance snd_proper : Proper ((≡@{A*B}) ==> (≡)) snd := _.

  Global Instance prod_swap_proper :
    Proper ((≡@{A*B}) ==> (≡@{B*A})) prod_swap := _.

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

  Lemma pair_equiv (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) ≡ (a2, b2) ↔ a1 ≡ a2 ∧ b1 ≡ b2.
  Proof. reflexivity. Qed.
End prod_setoid.

Global Typeclasses Opaque prod_equiv.

Global Instance prod_leibniz `{LeibnizEquiv A, LeibnizEquiv B} :
  LeibnizEquiv (A * B).
Proof. intros [??] [??] [??]; f_equal; apply leibniz_equiv; auto. Qed.

(** ** Sums *)
Definition sum_map {A A' B B'} (f: A → A') (g: B → B') (xy : A + B) : A' + B' :=
  match xy with inl x => inl (f x) | inr y => inr (g y) end.
Global Arguments sum_map {_ _ _ _} _ _ !_ / : assert.

Global Instance sum_inhabited_l {A B} (iA : Inhabited A) : Inhabited (A + B) :=
  match iA with populate x => populate (inl x) end.
Global Instance sum_inhabited_r {A B} (iB : Inhabited B) : Inhabited (A + B) :=
  match iB with populate y => populate (inr y) end.

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
End sum_relation.

Global Instance sum_equiv `{Equiv A, Equiv B} : Equiv (A + B) := sum_relation (≡) (≡).

Elpi Accumulate TC_solver lp:{{
    pred remove_equiv_sum_equiv i:term, o:term.
    remove_equiv_sum_equiv T1 T3 :-
      T1 = {{@equiv _ (@sum_equiv _ _ _ _)}}, !,
      T2 = {{@sum_relation lp:F lp:G lp:A lp:B}},
      coq.unify-eq T1 T2 ok, 
      remove_equiv_sum_equiv A X,
      remove_equiv_sum_equiv B Y,
      {{@sum_relation lp:F lp:G lp:X lp:Y}} = T3.
    remove_equiv_sum_equiv (app L1) (app L2) :- !,
      std.map L1 remove_equiv_sum_equiv L2.
    remove_equiv_sum_equiv A A.
    
    shorten tc-Coq.Classes.Morphisms.{tc-Proper}.
    :after "lastHook" 
    tc-Proper A B C R :-
      B = {{ @respectful _ _ _ _ }},
      remove_equiv_sum_equiv B B1,
      tc-Proper A B1 C R.
}}.
Elpi Typecheck TC_solver.


Global Instance inl_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@inl A B) := _.
Global Instance inr_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@inr A B) := _.


Elpi Accumulate TC_solver lp:{{
  shorten tc-elpi.apps.tc.tests.bigTest.{tc-Inj}.
  % shorten tc-bigTest.{tc-Inj}.
  :after "lastHook" 
  tc-Inj A B R1 R2 S C :-
    R2 = {{@equiv (sum _ _) sum_equiv}},
    R2' = {{sum_relation _ _}},
    coq.unify-eq R2 R2' ok,
    tc-Inj A B R1 R2' S C.
}}.
Elpi Typecheck TC_solver.

Global Instance inl_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inl A B) := _.
Global Instance inr_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inr A B) := _.
Global Typeclasses Opaque sum_equiv.

(** ** Option *)
Global Instance option_inhabited {A} : Inhabited (option A) := populate None.

(** ** Sigma types *)
Global Arguments existT {_ _} _ _ : assert.
Global Arguments projT1 {_ _} _ : assert.
Global Arguments projT2 {_ _} _ : assert.

Global Arguments exist {_} _ _ _ : assert.
Global Arguments proj1_sig {_ _} _ : assert.
Global Arguments proj2_sig {_ _} _ : assert.
Notation "x ↾ p" := (exist _ x p) (at level 20) : stdpp_scope.
Notation "` x" := (proj1_sig x) (at level 10, format "` x") : stdpp_scope.

Lemma proj1_sig_inj {A} (P : A → Prop) x (Px : P x) y (Py : P y) :
  x↾Px = y↾Py → x = y.
Proof. injection 1; trivial. Qed.

Section sig_map.
  Context `{P : A → Prop} `{Q : B → Prop} (f : A → B) (Hf : ∀ x, P x → Q (f x)).
  Definition sig_map (x : sig P) : sig Q := f (`x) ↾ Hf _ (proj2_sig x).
  Global Instance sig_map_inj:
    (∀ x, ProofIrrel (P x)) → Inj (=) (=) f → Inj (=) (=) sig_map.
  Proof.
    intros ?? [x Hx] [y Hy]. injection 1. intros Hxy.
    apply (inj f) in Hxy; subst. rewrite (proof_irrel _ Hy). auto.
  Qed.
End sig_map.
Global Arguments sig_map _ _ _ _ _ _ !_ / : assert.

Definition proj1_ex {P : Prop} {Q : P → Prop} (p : ∃ x, Q x) : P :=
  let '(ex_intro _ x _) := p in x.
Definition proj2_ex {P : Prop} {Q : P → Prop} (p : ∃ x, Q x) : Q (proj1_ex p) :=
  let '(ex_intro _ x H) := p in H.

(** * Operations on sets *)
(** We define operational type classes for the traditional operations and
relations on sets: the empty set [∅], the union [(∪)],
intersection [(∩)], and difference [(∖)], the singleton [{[_]}], the subset
[(⊆)] and element of [(∈)] relation, and disjointess [(##)]. *)
Class Empty A := empty: A.
Global Hint Mode Empty ! : typeclass_instances.
Notation "∅" := empty (format "∅") : stdpp_scope.

Global Instance empty_inhabited `(Empty A) : Inhabited A := populate ∅.

Class Union A := union: A → A → A.
Global Hint Mode Union ! : typeclass_instances.
Global Instance: Params (@union) 2 := {}.
Infix "∪" := union (at level 50, left associativity) : stdpp_scope.
Notation "(∪)" := union (only parsing) : stdpp_scope.
Notation "( x ∪.)" := (union x) (only parsing) : stdpp_scope.
Notation "(.∪ x )" := (λ y, union y x) (only parsing) : stdpp_scope.
Infix "∪*" := (zip_with (∪)) (at level 50, left associativity) : stdpp_scope.
Notation "(∪*)" := (zip_with (∪)) (only parsing) : stdpp_scope.

Definition union_list `{Empty A} `{Union A} : list A → A := fold_right (∪) ∅.
Global Arguments union_list _ _ _ !_ / : assert.
Notation "⋃ l" := (union_list l) (at level 20, format "⋃  l") : stdpp_scope.

Class Intersection A := intersection: A → A → A.
Global Hint Mode Intersection ! : typeclass_instances.
Global Instance: Params (@intersection) 2 := {}.
Infix "∩" := intersection (at level 40) : stdpp_scope.
Notation "(∩)" := intersection (only parsing) : stdpp_scope.
Notation "( x ∩.)" := (intersection x) (only parsing) : stdpp_scope.
Notation "(.∩ x )" := (λ y, intersection y x) (only parsing) : stdpp_scope.

Class Difference A := difference: A → A → A.
Global Hint Mode Difference ! : typeclass_instances.
Global Instance: Params (@difference) 2 := {}.
Infix "∖" := difference (at level 40, left associativity) : stdpp_scope.
Notation "(∖)" := difference (only parsing) : stdpp_scope.
Notation "( x ∖.)" := (difference x) (only parsing) : stdpp_scope.
Notation "(.∖ x )" := (λ y, difference y x) (only parsing) : stdpp_scope.
Infix "∖*" := (zip_with (∖)) (at level 40, left associativity) : stdpp_scope.
Notation "(∖*)" := (zip_with (∖)) (only parsing) : stdpp_scope.

Class Singleton A B := singleton: A → B.
Global Hint Mode Singleton - ! : typeclass_instances.
Global Instance: Params (@singleton) 3 := {}.
Notation "{[ x ]}" := (singleton x) (at level 1) : stdpp_scope.
Notation "{[ x ; y ; .. ; z ]}" :=
  (union .. (union (singleton x) (singleton y)) .. (singleton z))
  (at level 1) : stdpp_scope.

Class SubsetEq A := subseteq: relation A.
Global Hint Mode SubsetEq ! : typeclass_instances.
Global Instance: Params (@subseteq) 2 := {}.
Infix "⊆" := subseteq (at level 70) : stdpp_scope.
Notation "(⊆)" := subseteq (only parsing) : stdpp_scope.
Notation "( X ⊆.)" := (subseteq X) (only parsing) : stdpp_scope.
Notation "(.⊆ X )" := (λ Y, Y ⊆ X) (only parsing) : stdpp_scope.
Notation "X ⊈ Y" := (¬X ⊆ Y) (at level 70) : stdpp_scope.
Notation "(⊈)" := (λ X Y, X ⊈ Y) (only parsing) : stdpp_scope.
Notation "( X ⊈.)" := (λ Y, X ⊈ Y) (only parsing) : stdpp_scope.
Notation "(.⊈ X )" := (λ Y, Y ⊈ X) (only parsing) : stdpp_scope.

Infix "⊆@{ A }" := (@subseteq A _) (at level 70, only parsing) : stdpp_scope.
Notation "(⊆@{ A } )" := (@subseteq A _) (only parsing) : stdpp_scope.

Infix "⊆*" := (Forall2 (⊆)) (at level 70) : stdpp_scope.
Notation "(⊆*)" := (Forall2 (⊆)) (only parsing) : stdpp_scope.

Global Hint Extern 0 (_ ⊆ _) => reflexivity : core.
Global Hint Extern 0 (_ ⊆* _) => reflexivity : core.

Infix "⊂" := (strict (⊆)) (at level 70) : stdpp_scope.
Notation "(⊂)" := (strict (⊆)) (only parsing) : stdpp_scope.
Notation "( X ⊂.)" := (strict (⊆) X) (only parsing) : stdpp_scope.
Notation "(.⊂ X )" := (λ Y, Y ⊂ X) (only parsing) : stdpp_scope.
Notation "X ⊄ Y" := (¬X ⊂ Y) (at level 70) : stdpp_scope.
Notation "(⊄)" := (λ X Y, X ⊄ Y) (only parsing) : stdpp_scope.
Notation "( X ⊄.)" := (λ Y, X ⊄ Y) (only parsing) : stdpp_scope.
Notation "(.⊄ X )" := (λ Y, Y ⊄ X) (only parsing) : stdpp_scope.

Infix "⊂@{ A }" := (strict (⊆@{A})) (at level 70, only parsing) : stdpp_scope.
Notation "(⊂@{ A } )" := (strict (⊆@{A})) (only parsing) : stdpp_scope.

Notation "X ⊆ Y ⊆ Z" := (X ⊆ Y ∧ Y ⊆ Z) (at level 70, Y at next level) : stdpp_scope.
Notation "X ⊆ Y ⊂ Z" := (X ⊆ Y ∧ Y ⊂ Z) (at level 70, Y at next level) : stdpp_scope.
Notation "X ⊂ Y ⊆ Z" := (X ⊂ Y ∧ Y ⊆ Z) (at level 70, Y at next level) : stdpp_scope.
Notation "X ⊂ Y ⊂ Z" := (X ⊂ Y ∧ Y ⊂ Z) (at level 70, Y at next level) : stdpp_scope.

(** We define type classes for multisets: disjoint union [⊎] and the multiset
singleton [{[+ _ +]}]. Multiset literals [{[+ x1; ..; xn +]}] are defined in
terms of iterated disjoint union [{[+ x1 +]} ⊎ .. ⊎ {[+ xn +]}], and are thus
different from set literals [{[ x1; ..; xn ]}], which use [∪].

Note that in principle we could reuse the set singleton [{[ _ ]}] for multisets,
and define [{[+ x1; ..; xn +]}] as [{[ x1 ]} ⊎ .. ⊎ {[ xn ]}]. However, this
would risk accidentally using [{[ x1; ..; xn ]}] for multisets (leading to
unexpected results) and lead to ambigious pretty printing for [{[+ x +]}]. *)
Class DisjUnion A := disj_union: A → A → A.
Global Hint Mode DisjUnion ! : typeclass_instances.
Global Instance: Params (@disj_union) 2 := {}.
Infix "⊎" := disj_union (at level 50, left associativity) : stdpp_scope.
Notation "(⊎)" := disj_union (only parsing) : stdpp_scope.
Notation "( x ⊎.)" := (disj_union x) (only parsing) : stdpp_scope.
Notation "(.⊎ x )" := (λ y, disj_union y x) (only parsing) : stdpp_scope.

Class SingletonMS A B := singletonMS: A → B.
Global Hint Mode SingletonMS - ! : typeclass_instances.
Global Instance: Params (@singletonMS) 3 := {}.
Notation "{[+ x +]}" := (singletonMS x)
  (at level 1, format "{[+  x  +]}") : stdpp_scope.
Notation "{[+ x ; y ; .. ; z +]}" :=
  (disj_union .. (disj_union (singletonMS x) (singletonMS y)) .. (singletonMS z))
  (at level 1, format "{[+  x ;  y ;  .. ;  z  +]}") : stdpp_scope.

Definition option_to_set `{Singleton A C, Empty C} (mx : option A) : C :=
  match mx with None => ∅ | Some x => {[ x ]} end.
Fixpoint list_to_set `{Singleton A C, Empty C, Union C} (l : list A) : C :=
  match l with [] => ∅ | x :: l => {[ x ]} ∪ list_to_set l end.
Fixpoint list_to_set_disj `{SingletonMS A C, Empty C, DisjUnion C} (l : list A) : C :=
  match l with [] => ∅ | x :: l => {[+ x +]} ⊎ list_to_set_disj l end.

Class ScalarMul N A := scalar_mul : N → A → A.
Global Hint Mode ScalarMul - ! : typeclass_instances.
(** The [N] arguments is typically [nat] or [Z], so we do not want to rewrite
in that. Hence, the value of [Params] is 3. *)
Global Instance: Params (@scalar_mul) 3 := {}.
(** The notation [*:] and level is taken from ssreflect, see
https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnotations.v *)
Infix "*:" := scalar_mul (at level 40) : stdpp_scope.
Notation "(*:)" :=  scalar_mul (only parsing) : stdpp_scope.
Notation "( x *:.)" := (scalar_mul x) (only parsing) : stdpp_scope.
Notation "(.*: x )" := (λ y, scalar_mul y x) (only parsing) : stdpp_scope.

(** The class [Lexico A] is used for the lexicographic order on [A]. This order
is used to create finite maps, finite sets, etc, and is typically different from
the order [(⊆)]. *)
Class Lexico A := lexico: relation A.
Global Hint Mode Lexico ! : typeclass_instances.

Class ElemOf A B := elem_of: A → B → Prop.
Global Hint Mode ElemOf - ! : typeclass_instances.
Global Instance: Params (@elem_of) 3 := {}.
Infix "∈" := elem_of (at level 70) : stdpp_scope.
Notation "(∈)" := elem_of (only parsing) : stdpp_scope.
Notation "( x ∈.)" := (elem_of x) (only parsing) : stdpp_scope.
Notation "(.∈ X )" := (λ x, elem_of x X) (only parsing) : stdpp_scope.
Notation "x ∉ X" := (¬x ∈ X) (at level 80) : stdpp_scope.
Notation "(∉)" := (λ x X, x ∉ X) (only parsing) : stdpp_scope.
Notation "( x ∉.)" := (λ X, x ∉ X) (only parsing) : stdpp_scope.
Notation "(.∉ X )" := (λ x, x ∉ X) (only parsing) : stdpp_scope.

Infix "∈@{ B }" := (@elem_of _ B _) (at level 70, only parsing) : stdpp_scope.
Notation "(∈@{ B } )" := (@elem_of _ B _) (only parsing) : stdpp_scope.

Notation "x ∉@{ B } X" := (¬x ∈@{B} X) (at level 80, only parsing) : stdpp_scope.
Notation "(∉@{ B } )" := (λ x X, x ∉@{B} X) (only parsing) : stdpp_scope.

Class Disjoint A := disjoint : A → A → Prop.
Global Hint Mode Disjoint ! : typeclass_instances.
Global Instance: Params (@disjoint) 2 := {}.
Infix "##" := disjoint (at level 70) : stdpp_scope.
Notation "(##)" := disjoint (only parsing) : stdpp_scope.
Notation "( X ##.)" := (disjoint X) (only parsing) : stdpp_scope.
Notation "(.## X )" := (λ Y, Y ## X) (only parsing) : stdpp_scope.

Infix "##@{ A }" := (@disjoint A _) (at level 70, only parsing) : stdpp_scope.
Notation "(##@{ A } )" := (@disjoint A _) (only parsing) : stdpp_scope.

Infix "##*" := (Forall2 (##)) (at level 70) : stdpp_scope.
Notation "(##*)" := (Forall2 (##)) (only parsing) : stdpp_scope.

Global Hint Extern 0 (_ ## _) => symmetry; eassumption : core.
Global Hint Extern 0 (_ ##* _) => symmetry; eassumption : core.

Class Filter A B := filter: ∀ (P : A → Prop) `{∀ x, Decision (P x)}, B → B.
Global Hint Mode Filter - ! : typeclass_instances.

Class UpClose A B := up_close : A → B.
Global Hint Mode UpClose - ! : typeclass_instances.
Notation "↑ x" := (up_close x) (at level 20, format "↑ x").

(** * Monadic operations *)
(** We define operational type classes for the monadic operations bind, join
and fmap. We use these type classes merely for convenient overloading of
notations and do not formalize any theory on monads (we do not even define a
class with the monad laws). *)
Class MRet (M : Type → Type) := mret: ∀ {A}, A → M A.
Global Arguments mret {_ _ _} _ : assert.
Global Instance: Params (@mret) 3 := {}.
Global Hint Mode MRet ! : typeclass_instances.

Class MBind (M : Type → Type) := mbind : ∀ {A B}, (A → M B) → M A → M B.
Global Arguments mbind {_ _ _ _} _ !_ / : assert.
Global Instance: Params (@mbind) 4 := {}.
Global Hint Mode MBind ! : typeclass_instances.

Class MJoin (M : Type → Type) := mjoin: ∀ {A}, M (M A) → M A.
Global Arguments mjoin {_ _ _} !_ / : assert.
Global Instance: Params (@mjoin) 3 := {}.
Global Hint Mode MJoin ! : typeclass_instances.

Class FMap (M : Type → Type) := fmap : ∀ {A B}, (A → B) → M A → M B.
Global Arguments fmap {_ _ _ _} _ !_ / : assert.
Global Instance: Params (@fmap) 4 := {}.
Global Hint Mode FMap ! : typeclass_instances.

Class OMap (M : Type → Type) := omap: ∀ {A B}, (A → option B) → M A → M B.
Global Arguments omap {_ _ _ _} _ !_ / : assert.
Global Instance: Params (@omap) 4 := {}.
Global Hint Mode OMap ! : typeclass_instances.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=.)" := (λ f, mbind f m) (only parsing) : stdpp_scope.
Notation "(.≫= f )" := (mbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, mbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.

Infix "<$>" := fmap (at level 61, left associativity) : stdpp_scope.

Notation "x ;; z" := (x ≫= λ _, z)
  (at level 100, z at level 200, only parsing, right associativity): stdpp_scope.

Notation "ps .*1" := (fmap (M:=list) fst ps)
  (at level 2, left associativity, format "ps .*1").
Notation "ps .*2" := (fmap (M:=list) snd ps)
  (at level 2, left associativity, format "ps .*2").

(** For any monad that has a builtin way to throw an exception/error *)
Class MThrow (E : Type) (M : Type → Type) := mthrow : ∀ {A}, E → M A.
Global Arguments mthrow {_ _ _ _} _ : assert.
Global Instance: Params (@mthrow) 4 := {}.
Global Hint Mode MThrow ! ! : typeclass_instances.

(** We use unit as the error content for monads that can only report an error
    without any payload like an option *)
Global Notation MFail := (MThrow ()).
Global Notation mfail := (mthrow ()).

Definition guard_or {E} (e : E) `{MThrow E M, MRet M} P `{Decision P} : M P :=
  match decide P with
  | left H => mret H
  | right _ => mthrow e
  end.
Global Notation guard := (guard_or ()).


(** * Operations on maps *)
(** In this section we define operational type classes for the operations
on maps. In the file [fin_maps] we will axiomatize finite maps.
The function look up [m !! k] should yield the element at key [k] in [m]. *)
Class Lookup (K A M : Type) := lookup: K → M → option A.
Global Hint Mode Lookup - - ! : typeclass_instances.
Global Instance: Params (@lookup) 5 := {}.
Notation "m !! i" := (lookup i m) (at level 20) : stdpp_scope.
Notation "(!!)" := lookup (only parsing) : stdpp_scope.
Notation "( m !!.)" := (λ i, m !! i) (only parsing) : stdpp_scope.
Notation "(.!! i )" := (lookup i) (only parsing) : stdpp_scope.
Global Arguments lookup _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [lookup_total] should be the total over-approximation
of the partial [lookup] function. *)
Class LookupTotal (K A M : Type) := lookup_total : K → M → A.
Global Hint Mode LookupTotal - - ! : typeclass_instances.
Global Instance: Params (@lookup_total) 5 := {}.
Notation "m !!! i" := (lookup_total i m) (at level 20) : stdpp_scope.
Notation "(!!!)" := lookup_total (only parsing) : stdpp_scope.
Notation "( m !!!.)" := (λ i, m !!! i) (only parsing) : stdpp_scope.
Notation "(.!!! i )" := (lookup_total i) (only parsing) : stdpp_scope.
Global Arguments lookup_total _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The singleton map *)
Class SingletonM K A M := singletonM: K → A → M.
Global Hint Mode SingletonM - - ! : typeclass_instances.
Global Instance: Params (@singletonM) 5 := {}.
Notation "{[ k := a ]}" := (singletonM k a) (at level 1) : stdpp_scope.

(** The function insert [<[k:=a]>m] should update the element at key [k] with
value [a] in [m]. *)
Class Insert (K A M : Type) := insert: K → A → M → M.
Global Hint Mode Insert - - ! : typeclass_instances.
Global Instance: Params (@insert) 5 := {}.
Notation "<[ k := a ]>" := (insert k a)
  (at level 5, right associativity, format "<[ k := a ]>") : stdpp_scope.
Global Arguments insert _ _ _ _ !_ _ !_ / : simpl nomatch, assert.

(** Notation for more elements (up to 13) *)
(* Defining a generic notation does not seem possible with Coq's
   recursive notation system, so we define individual notations
   for some cases relevant in practice. *)
(* The "format" makes sure that linebreaks are placed after the separating semicola [;] when printing. *)
(* TODO : we are using parantheses in the "de-sugaring" of the notation instead of [$] because Coq 8.12
   and earlier have trouble with using the notation for printing otherwise.
   Once support for Coq 8.12 is dropped, this can be replaced with [$]. *)
Notation "{[ k1 := a1 ; k2 := a2 ]}" :=
  (<[ k1 := a1 ]>{[ k2 := a2 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]>{[ k3 := a3 ]}))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]>{[ k4 := a4 ]})))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]>{[ k5 := a5 ]}))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]>{[ k6 := a6 ]})))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]>{[ k7 := a7 ]}))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ; k8 := a8 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]> ( <[ k7 := a7 ]>{[ k8 := a8 ]})))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ; ']'  '/' '[' k8  :=  a8 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ; k8 := a8 ; k9 := a9 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]> ( <[ k7 := a7 ]> ( <[ k8 := a8 ]>{[ k9 := a9 ]}))))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ; ']'  '/' '[' k8  :=  a8 ; ']'  '/' '[' k9  :=  a9 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ; k8 := a8 ; k9 := a9 ; k10 := a10 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]> ( <[ k7 := a7 ]> ( <[ k8 := a8 ]> (
    <[ k9 := a9 ]>{[ k10 := a10 ]})))))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ; ']'  '/' '[' k8  :=  a8 ; ']'  '/' '[' k9  :=  a9 ; ']'  '/' '[' k10  :=  a10 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ; k8 := a8 ; k9 := a9 ; k10 := a10 ; k11 := a11 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]> ( <[ k7 := a7 ]> ( <[ k8 := a8 ]> (
    <[ k9 := a9 ]> ( <[ k10 := a10 ]>{[ k11 := a11 ]}))))))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ; ']'  '/' '[' k8  :=  a8 ; ']'  '/' '[' k9  :=  a9 ; ']'  '/' '[' k10  :=  a10 ; ']'  '/' '[' k11  :=  a11 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ; k8 := a8 ; k9 := a9 ; k10 := a10 ; k11 := a11 ; k12 := a12 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]> ( <[ k7 := a7 ]> ( <[ k8 := a8 ]> (
    <[ k9 := a9 ]> ( <[ k10 := a10 ]> ( <[ k11 := a11 ]>{[ k12 := a12 ]})))))))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ; ']'  '/' '[' k8  :=  a8 ; ']'  '/' '[' k9  :=  a9 ; ']'  '/' '[' k10  :=  a10 ; ']'  '/' '[' k11  :=  a11 ; ']'  '/' '[' k12  :=  a12 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 := a1 ; k2 := a2 ; k3 := a3 ; k4 := a4 ; k5 := a5 ; k6 := a6 ; k7 := a7 ; k8 := a8 ; k9 := a9 ; k10 := a10 ; k11 := a11 ; k12 := a12 ; k13 := a13 ]}" :=
  (<[ k1 := a1 ]> ( <[ k2 := a2 ]> ( <[ k3 := a3 ]> ( <[ k4 := a4 ]> (
    <[ k5 := a5 ]> ( <[ k6 := a6 ]> ( <[ k7 := a7 ]> ( <[ k8 := a8 ]> (
    <[ k9 := a9 ]> ( <[ k10 := a10 ]> ( <[ k11 := a11 ]> ( <[ k12 := a12 ]>{[ k13 := a13 ]}))))))))))))
  (at level 1, format
  "{[ '[hv' '[' k1  :=  a1 ; ']'  '/' '[' k2  :=  a2 ; ']'  '/' '[' k3  :=  a3 ; ']'  '/' '[' k4  :=  a4 ; ']'  '/' '[' k5  :=  a5 ; ']'  '/' '[' k6  :=  a6 ; ']'  '/' '[' k7  :=  a7 ; ']'  '/' '[' k8  :=  a8 ; ']'  '/' '[' k9  :=  a9 ; ']'  '/' '[' k10  :=  a10 ; ']'  '/' '[' k11  :=  a11 ; ']'  '/' '[' k12  :=  a12 ; ']'  '/' '[' k13  :=  a13 ']' ']' ]}") : stdpp_scope.

(** The function delete [delete k m] should delete the value at key [k] in
[m]. If the key [k] is not a member of [m], the original map should be
returned. *)
Class Delete (K M : Type) := delete: K → M → M.
Global Hint Mode Delete - ! : typeclass_instances.
Global Instance: Params (@delete) 4 := {}.
Global Arguments delete _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [alter f k m] should update the value at key [k] using the
function [f], which is called with the original value. *)
Class Alter (K A M : Type) := alter: (A → A) → K → M → M.
Global Hint Mode Alter - - ! : typeclass_instances.
Global Instance: Params (@alter) 4 := {}.
Global Arguments alter {_ _ _ _} _ !_ !_ / : simpl nomatch, assert.

(** The function [partial_alter f k m] should update the value at key [k] using the
function [f], which is called with the original value at key [k] or [None]
if [k] is not a member of [m]. The value at [k] should be deleted if [f]
yields [None]. *)
Class PartialAlter (K A M : Type) :=
  partial_alter: (option A → option A) → K → M → M.
Global Hint Mode PartialAlter - - ! : typeclass_instances.
Global Instance: Params (@partial_alter) 4 := {}.
Global Arguments partial_alter _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [dom m] should yield the domain of [m]. That is a finite
set of type [D] that contains the keys that are a member of [m].
[D] is an output of the typeclass, i.e., there can be only one instance per map
type [M]. *)
Class Dom (M D : Type) := dom: M → D.
Global Hint Mode Dom ! - : typeclass_instances.
Global Instance: Params (@dom) 3 := {}.
Global Arguments dom : clear implicits.
Global Arguments dom {_ _ _} !_ / : simpl nomatch, assert.

(** The function [merge f m1 m2] should merge the maps [m1] and [m2] by
constructing a new map whose value at key [k] is [f (m1 !! k) (m2 !! k)].*)
Class Merge (M : Type → Type) :=
  merge: ∀ {A B C}, (option A → option B → option C) → M A → M B → M C.
Global Hint Mode Merge ! : typeclass_instances.
Global Instance: Params (@merge) 4 := {}.
Global Arguments merge _ _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [union_with f m1 m2] is supposed to yield the union of [m1]
and [m2] using the function [f] to combine values of members that are in
both [m1] and [m2]. *)
Class UnionWith (A M : Type) :=
  union_with: (A → A → option A) → M → M → M.
Global Hint Mode UnionWith - ! : typeclass_instances.
Global Instance: Params (@union_with) 3 := {}.
Global Arguments union_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

(** Similarly for intersection and difference. *)
Class IntersectionWith (A M : Type) :=
  intersection_with: (A → A → option A) → M → M → M.
Global Hint Mode IntersectionWith - ! : typeclass_instances.
Global Instance: Params (@intersection_with) 3 := {}.
Global Arguments intersection_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

Class DifferenceWith (A M : Type) :=
  difference_with: (A → A → option A) → M → M → M.
Global Hint Mode DifferenceWith - ! : typeclass_instances.
Global Instance: Params (@difference_with) 3 := {}.
Global Arguments difference_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

Definition intersection_with_list `{IntersectionWith A M}
  (f : A → A → option A) : M → list M → M := fold_right (intersection_with f).
Global Arguments intersection_with_list _ _ _ _ _ !_ / : assert.

(** * Notations for lattices. *)
(** SqSubsetEq registers the "canonical" partial order for a type, and is used
for the \sqsubseteq symbol. *)
Class SqSubsetEq A := sqsubseteq: relation A.
Global Hint Mode SqSubsetEq ! : typeclass_instances.
Global Instance: Params (@sqsubseteq) 2 := {}.
Infix "⊑" := sqsubseteq (at level 70) : stdpp_scope.
Notation "(⊑)" := sqsubseteq (only parsing) : stdpp_scope.
Notation "( x ⊑.)" := (sqsubseteq x) (only parsing) : stdpp_scope.
Notation "(.⊑ y )" := (λ x, sqsubseteq x y) (only parsing) : stdpp_scope.

Infix "⊑@{ A }" := (@sqsubseteq A _) (at level 70, only parsing) : stdpp_scope.
Notation "(⊑@{ A } )" := (@sqsubseteq A _) (only parsing) : stdpp_scope.

(** [sqsubseteq] does not take precedence over the stdlib's instances (like [eq],
[impl], [iff]) or std++'s [equiv].
We have [eq] (at 100) < [≡] (at 150) < [⊑] (at 200). *)
Global Instance sqsubseteq_rewrite `{SqSubsetEq A} : RewriteRelation (⊑@{A}) | 200 := {}.

Global Hint Extern 0 (_ ⊑ _) => reflexivity : core.

Class Meet A := meet: A → A → A.
Global Hint Mode Meet ! : typeclass_instances.
Global Instance: Params (@meet) 2 := {}.
Infix "⊓" := meet (at level 40) : stdpp_scope.
Notation "(⊓)" := meet (only parsing) : stdpp_scope.
Notation "( x ⊓.)" := (meet x) (only parsing) : stdpp_scope.
Notation "(.⊓ y )" := (λ x, meet x y) (only parsing) : stdpp_scope.

Class Join A := join: A → A → A.
Global Hint Mode Join ! : typeclass_instances.
Global Instance: Params (@join) 2 := {}.
Infix "⊔" := join (at level 50) : stdpp_scope.
Notation "(⊔)" := join (only parsing) : stdpp_scope.
Notation "( x ⊔.)" := (join x) (only parsing) : stdpp_scope.
Notation "(.⊔ y )" := (λ x, join x y) (only parsing) : stdpp_scope.

Class Top A := top : A.
Global Hint Mode Top ! : typeclass_instances.
Notation "⊤" := top (format "⊤") : stdpp_scope.

Class Bottom A := bottom : A.
Global Hint Mode Bottom ! : typeclass_instances.
Notation "⊥" := bottom (format "⊥") : stdpp_scope.


(** * Axiomatization of sets *)
(** The classes [SemiSet A C], [Set_ A C], and [TopSet A C] axiomatize sets of
type [C] with elements of type [A]. The first class, [SemiSet] does not include
intersection and difference. It is useful for the case of lists, where decidable
equality is needed to implement intersection and difference, but not union.

Note that we cannot use the name [Set] since that is a reserved keyword. Hence
we use [Set_]. *)
Class SemiSet A C `{ElemOf A C,
    Empty C, Singleton A C, Union C} : Prop := {
  not_elem_of_empty (x : A) : x ∉@{C} ∅; (* We prove
  [elem_of_empty : x ∈@{C} ∅ ↔ False] in [sets.v], which is more convenient for
  rewriting. *)
  elem_of_singleton (x y : A) : x ∈@{C} {[ y ]} ↔ x = y;
  elem_of_union (X Y : C) (x : A) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
}.
Global Hint Mode SemiSet - ! - - - - : typeclass_instances.

Class Set_ A C `{ElemOf A C, Empty C, Singleton A C,
    Union C, Intersection C, Difference C} : Prop := {
  set_semi_set :> SemiSet A C;
  elem_of_intersection (X Y : C) (x : A) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y;
  elem_of_difference (X Y : C) (x : A) : x ∈ X ∖ Y ↔ x ∈ X ∧ x ∉ Y
}.
Global Hint Mode Set_ - ! - - - - - - : typeclass_instances.

Class TopSet A C `{ElemOf A C, Empty C, Top C, Singleton A C,
    Union C, Intersection C, Difference C} : Prop := {
  top_set_set :> Set_ A C;
  elem_of_top' (x : A) : x ∈@{C} ⊤; (* We prove [elem_of_top : x ∈@{C} ⊤ ↔ True]
  in [sets.v], which is more convenient for rewriting. *)
}.
Global Hint Mode TopSet - ! - - - - - - - : typeclass_instances.

(** We axiomative a finite set as a set whose elements can be
enumerated as a list. These elements, given by the [elements] function, may be
in any order and should not contain duplicates. *)
Class Elements A C := elements: C → list A.
Global Hint Mode Elements - ! : typeclass_instances.
Global Instance: Params (@elements) 3 := {}.

(** We redefine the standard library's [In] and [NoDup] using type classes. *)
Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here (x : A) l : x ∈ x :: l
  | elem_of_list_further (x y : A) l : x ∈ l → x ∈ y :: l.
Global Existing Instance elem_of_list.

Lemma elem_of_list_In {A} (l : list A) x : x ∈ l ↔ In x l.
Proof.
  split.
  - induction 1; simpl; auto.
  - induction l; destruct 1; subst; constructor; auto.
Qed.

Inductive NoDup {A} : list A → Prop :=
  | NoDup_nil_2 : NoDup []
  | NoDup_cons_2 x l : x ∉ l → NoDup l → NoDup (x :: l).

Lemma NoDup_ListNoDup {A} (l : list A) : NoDup l ↔ List.NoDup l.
Proof.
  split.
  - induction 1; constructor; rewrite <-?elem_of_list_In; auto.
  - induction 1; constructor; rewrite ?elem_of_list_In; auto.
Qed.

(** Decidability of equality of the carrier set is admissible, but we add it
anyway so as to avoid cycles in type class search. *)
Class FinSet A C `{ElemOf A C, Empty C, Singleton A C, Union C,
    Intersection C, Difference C, Elements A C, EqDecision A} : Prop := {
  fin_set_set :> Set_ A C;
  elem_of_elements (X : C) x : x ∈ elements X ↔ x ∈ X;
  NoDup_elements (X : C) : NoDup (elements X)
}.
Global Hint Mode FinSet - ! - - - - - - - - : typeclass_instances.

Class Size C := size: C → nat.
Global Hint Mode Size ! : typeclass_instances.
Global Arguments size {_ _} !_ / : simpl nomatch, assert.
Global Instance: Params (@size) 2 := {}.

(** The class [MonadSet M] axiomatizes a type constructor [M] that can be
used to construct a set [M A] with elements of type [A]. The advantage
of this class, compared to [Set_], is that it also axiomatizes the
the monadic operations. The disadvantage is that not many inhabitants are
possible: we will only provide as inhabitants [propset] and [listset], which are
represented respectively using Boolean functions and lists with duplicates.

More interesting implementations typically need
decidable equality, or a total order on the elements, which do not fit
in a type constructor of type [Type → Type]. *)
Class MonadSet M `{∀ A, ElemOf A (M A),
    ∀ A, Empty (M A), ∀ A, Singleton A (M A), ∀ A, Union (M A),
    !MBind M, !MRet M, !FMap M, !MJoin M} : Prop := {
  monad_set_semi_set A :> SemiSet A (M A);
  elem_of_bind {A B} (f : A → M B) (X : M A) (x : B) :
    x ∈ X ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ X;
  elem_of_ret {A} (x y : A) : x ∈@{M A} mret y ↔ x = y;
  elem_of_fmap {A B} (f : A → B) (X : M A) (x : B) :
    x ∈ f <$> X ↔ ∃ y, x = f y ∧ y ∈ X;
  elem_of_join {A} (X : M (M A)) (x : A) :
    x ∈ mjoin X ↔ ∃ Y : M A, x ∈ Y ∧ Y ∈ X
}.

(** The [Infinite A] class axiomatizes types [A] with infinitely many elements.
It contains a function [fresh : list A → A] that given a list [xs] gives an
element [fresh xs ∉ xs].

We do not directly make [fresh] a field of the [Infinite] class, but use a
separate operational type class [Fresh] for it. That way we can overload [fresh]
to pick fresh elements from other data structure like sets. See the file
[fin_sets], where we define [fresh : C → A] for any finite set implementation
[FinSet C A].

Note: we require [fresh] to respect permutations, which is needed to define the
aforementioned [fresh] function on finite sets that respects set equality.

Instead of instantiating [Infinite] directly, consider using [max_infinite] or
[inj_infinite] from the [infinite] module. *)
Class Fresh A C := fresh: C → A.
Global Hint Mode Fresh - ! : typeclass_instances.
Global Instance: Params (@fresh) 3 := {}.
Global Arguments fresh : simpl never.

Class Infinite A := {
  infinite_fresh :> Fresh A (list A);
  infinite_is_fresh (xs : list A) : fresh xs ∉ xs;
  infinite_fresh_Permutation :> Proper (@Permutation A ==> (=)) fresh;
}.
Global Hint Mode Infinite ! : typeclass_instances.
Global Arguments infinite_fresh : simpl never.

(** * Miscellaneous *)
Class Half A := half: A → A.
Global Hint Mode Half ! : typeclass_instances.
Notation "½" := half (format "½") : stdpp_scope.
Notation "½*" := (fmap (M:=list) half) : stdpp_scope.
