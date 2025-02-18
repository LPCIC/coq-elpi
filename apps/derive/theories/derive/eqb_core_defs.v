From elpi.core Require Import PosDef.
Require Import ssreflect ssrbool.
From elpi.apps.derive Require Import EqdepFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {A:Type}.

Definition eqb_correct_on (eqb : A -> A -> bool) (a1:A) := 
   forall a2, eqb a1 a2 -> a1 = a2.

Definition eqb_refl_on (eqb : A -> A -> bool) (a:A) := 
  is_true (eqb a a).

Definition eqb_correct (eqb : A -> A -> bool) := 
  forall (a1:A), eqb_correct_on eqb a1.
  
Definition eqb_reflexive (eqb : A -> A -> bool) := 
  forall (a:A), eqb_refl_on eqb a. 
 
Lemma iffP2 (f : A -> A -> bool) (H1 : eqb_correct f) (H2 : eqb_reflexive f)
 (x1 x2 : A) : reflect (x1 = x2) (f x1 x2).
Proof. apply (iffP idP);[ apply H1 | move->; apply H2 ]. Qed.

Definition eqax_on (eqb : A -> A -> bool) (a1:A) := 
   forall a2, reflect (a1 = a2) (eqb a1 a2).

End Section.

Lemma pos_eq_dec : forall x y:positive, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Theorem UIP_dec (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall (x y : A) (p1 p2 : x = y), p1 = p2.
Proof. exact (eq_dep_eq__UIP A (eq_dep_eq_dec eq_dec)). Qed.

Theorem bool_dec (b1 b2 : bool) : {b1 = b2} + {b1 <> b2}.
Proof. decide equality. Qed.

Section Section.
Context {A B:Type}.

Variable tagA       : A -> positive.
Variable tagB       : B -> positive.

Variable fields_tA  : positive -> Type.
Variable fields_tB  : positive -> Type.

Variable fieldsA    : forall a, fields_tA (tagA a).
Variable fieldsB    : forall a, fields_tB (tagB a).

Variable constructA : forall t, fields_tA t -> option A.
Variable constructB : forall t, fields_tB t -> option B.

Variable constructPA : forall a, constructA (fieldsA a) = Some a.
Variable constructPB : forall a, constructB (fieldsB a) = Some a.

Variable eqb_fields : forall t, fields_tA t -> fields_tB t -> bool.

Definition eqb_body (t1:positive) (f1:fields_tA t1) (x2:B) :=
  let t2 := tagB x2 in
  match pos_eq_dec t2 t1 with
  | left heq =>
    let f2 : fields_tB t2 := fieldsB x2 in
    @eqb_fields t1 f1 (match heq with eq_refl => f2 end)
  | right _ => false
  end.
#[global] Arguments eqb_body _ _ _ /.

End Section.

Section Section.
Context {A:Type}.

Variable tag       : A -> positive.

Variable fields_t  : positive -> Type.

Variable fields    : forall a, fields_t (tag a).

Variable construct : forall t, fields_t t -> option A.

Variable constructP : forall a, construct (fields a) = Some a.

Variable eqb_fields : forall t, fields_t t -> fields_t t -> bool.


Definition eqb_fields_correct_on (a:A) := 
  forall f : fields_t (tag a), 
    eqb_fields (fields a) f -> Some a = construct f.

Lemma eqb_body_correct a1 : 
  eqb_fields_correct_on a1 ->
  forall a2, eqb_body fields eqb_fields (fields a1) a2 -> a1 = a2.
Proof.
  move=> hf a2 hb.
  suff : Some a1 = Some a2 by move=> [->].
  rewrite -(constructP a2); move: hb; rewrite /eqb_body.
  case: pos_eq_dec => // heq.
  move: (tag a2) heq (fields a2) => t2 ?; subst t2 => f2 /=; apply hf.
Qed.

Definition eqb_fields_refl_on (a:A) := 
  eqb_fields (fields a) (fields a).

Lemma eqb_body_refl a :
  eqb_fields_refl_on a ->
  eqb_body fields eqb_fields (fields a) a.
Proof.
  pose h := constructP. (* dummy dependence to have the same type as eqb_body_correct *)
  rewrite /eqb_body => hf.
  case: pos_eq_dec => // heq.
  have -> /= := UIP_dec pos_eq_dec heq eq_refl; apply hf.
Qed.

Inductive blist := bnil | bcons (b : bool) (bs : blist).

Fixpoint eqb_refl_statement (acc : bool) (l : blist) {struct l} := 
  match l with 
  | bnil => acc = true
  | bcons b bs => b = true -> eqb_refl_statement (b && acc) bs
  end.

Lemma eqb_refl_statementP l : eqb_refl_statement true l.
Proof. elim: l => //= b l hrec ->; apply hrec. Qed.

Fixpoint implies (l : blist) (P : Prop) : Prop := 
  match l with 
  | bnil => P
  | bcons b bs => b = true -> implies bs P
  end.

Fixpoint allr (l : blist) :=
  match l with
  | bnil => true
  | bcons b bs => b && allr bs
  end.

Lemma impliesP (l:blist) (P:Prop) : implies l P -> allr l = true -> P.
Proof. by elim: l => //= b l hrec hall /andP[/hall]. Qed.

Inductive tlist := tnil | tcons (T : Type) (TS : tlist).

Fixpoint p_type (T : tlist) := 
  match T with
  | tnil => Prop
  | tcons T Ts => T -> p_type Ts
  end.

Fixpoint eq_ind_r_n (T : tlist) : p_type T -> p_type T -> Prop :=
  match T return p_type T -> p_type T -> Prop with
  | tnil       => fun p q => p -> q
  | tcons T Ts => fun p q => forall (x y : T), x = y -> @eq_ind_r_n Ts (p x) (q y)
  end.
 
Lemma eq_ind_r_nP (T : tlist) (p : p_type T) : @eq_ind_r_n T p p.
Proof. elim: T p => //= T Ts hrec f a1 a2 ->; apply hrec. Qed.

End Section.
