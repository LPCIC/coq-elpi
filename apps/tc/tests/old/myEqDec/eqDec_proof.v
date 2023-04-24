Require Export Bool Arith List.
From Coq Require Import FunctionalExtensionality.

Export ListNotations.
Generalizable Variables A B.

Class EqDec A : Type := {
  eqb : A -> A -> bool; 
  eqb_leibniz : forall x y, eqb x y = true -> x = y 
}.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Definition neqb {A} `{EqDec A} (x y : A) := negb (x == y). 

#[global, refine] Instance eq_unit : EqDec unit := { eqb x y := true }.
Proof.
  intros [] []; easy.
Defined.

#[global, refine] Instance eq_bool : EqDec bool := { eqb x y := if x then y else negb y }.
Proof.
  intros [] []; easy.
Defined.

#[global, refine] Instance eq_prod `(EqDec A, EqDec B) : EqDec (A * B) := { 
  eqb x y := 
  match x, y return bool with 
    | (la, ra), (lb, rb) => (la == lb) && (ra == rb) 
  end }.
Proof.
  intros [] [].
  (* Search (_ && _ = true). *)
  (* Search ((_ , _) = (_, _)). *)
  rewrite andb_true_iff, pair_equal_spec.
  intros.
  rewrite (eqb_leibniz a a0), (eqb_leibniz b b0).
  all: easy.
Defined.

#[global, refine] Instance eq_nat : EqDec nat := {
  eqb := fix aux i1 i2 := 
  match i1, i2 return bool with
    | O, O => true 
    | S x, S y => aux x y
    | _, _ => false 
  end 
}.
Proof.
  induction x; destruct y; try easy.
  simpl; intros.
  apply f_equal, IHx; easy.
Defined.

#[global, refine] Instance eq_list `(eqa : (EqDec A)) : EqDec (list A) :=
  { eqb := fix aux (x y : list A) :=
    match x, y return bool with
    | [], [] => true 
    | x :: xs, y :: ys => (eqb x y) && (aux xs ys)
    | _, _ => false
    end }.
Proof.
  induction x; intros; destruct y; try easy.
  assert (simplList: forall (a: A) xs b ys, a = b /\ xs = ys -> a :: xs = b :: ys).
  intros h1 t1 h2 t2 MyH.
  destruct MyH as [HD TL].
  rewrite HD, TL.
  easy.
  apply simplList.
  rewrite andb_true_iff in H.
  split.
  apply (eqb_leibniz a a0); easy.
  apply IHx; easy.
Defined.

Inductive bin {A} : Type := 
  | L : bin 
  | N : A -> bin -> bin -> bin.

#[global, refine] Instance eq_bin `(eqa : (EqDec A)) : EqDec (@bin A) :=
  { eqb := fix aux (x y : @bin A) :=
    match x, y return bool with
    | L, L => true 
    | N a b c, N d e f => (a == d) && (aux b e) && (aux c f)
    | _, _ => false
    end }.
Proof.
  induction x; intros; destruct y; try easy.
  repeat rewrite andb_true_iff in H.
  assert (aa0: a = a0) by now apply (eqb_leibniz a a0).
  assert (x1y1: x1 = y1) by now apply IHx1.
  assert (x2y2: x2 = y2) by now apply IHx2.
  rewrite aa0, x1y1, x2y2.
  easy.
Defined.

Inductive bin2 {A : Type} {B: Type}: Type := 
  | L1 : bin2
  | N1 : A -> @bin A -> @bin B -> bin2.

#[global, refine] Instance eq_bin2 `(eqa : EqDec A, eqb: EqDec B) : EqDec (@bin2 A B) :=
  { eqb (x y: @bin2 A B):= 
    match x, y return bool with
    | L1, L1 => true 
    | N1 a b c, N1 d e f => (a == d) && (b == e) && (c == f)
    | _, _ => false
    end }.
Proof.
  destruct x, y; intros; try easy.
  repeat rewrite andb_true_iff in H.
  assert (aa0: a = a0) by now apply (eqb_leibniz a a0).
  assert (bb1: b = b1) by now apply (eqb_leibniz b b1).
  assert (b0b2: b0 = b2) by now apply (eqb_leibniz b0 b2).
  rewrite aa0, bb1, b0b2.
  easy.
Defined.

(* The type for Letters *)
Inductive letter {A : Type} : Type := 
  | LA : A -> letter
  | LB : A -> letter
  | XA : letter
  | XB : letter
  | XC : letter.

#[global, refine] Instance eq_letter `(eqA : EqDec A) : EqDec (@letter A) := 
  { eqb x y :=  
    match x, y return bool with 
    | LA a, LA b | LB a, LB b => a == b
    | XA, XA | XB, XB | XC, XC => true
    | _, _ => false
    end}.
destruct x, y; try (apply f_equal); try easy.
all : intros; rewrite (eqb_leibniz a a0); easy.
Defined.

#[global, refine] Instance eq_bool_to_bool `(EqDec A) : EqDec (bool -> A) :=
{
  eqb f g := (f true == g true) && (f false == g false)
}.
Proof.
  intros x y Hyp.
  (* Search _ inside FunctionalExtensionality. *)
  apply functional_extensionality.
  rewrite andb_true_iff in Hyp.
  intros [].
  all : now apply (eqb_leibniz (x _) (y _)).
Defined.