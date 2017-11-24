Require Import elpi	. (*elpi.derive.eq elpi.derive.projK elpi.derive.isK.

Require Import Bool List ssreflect.

Definition axiom T eqb x := forall (y : T), reflect (x = y) (eqb x y).

Lemma reflect_eq_f1 T rT (f : T -> rT) x y (inj_f : f x = f y -> x = y) b :
  reflect (x = y) b -> reflect (f x = f y) b.
Proof.
case=> [ -> | abs ]; first by constructor 1.
by constructor 2 => /inj_f .
Qed.

Lemma reflect_eq_f2 T rT (f : T -> rT) x y 
   (inj_f : f x = f y -> x = y) b1 b2 :
  reflect (f = f) b1 ->
  reflect (x = y) b2 -> reflect (f x = f y) (b1 && b2).
Proof.
by case=> [ E1 | abs1 ]; case=> [ -> | abs2 ]; constructor => //; try move/inj_f.
Qed.

Elpi derive.eq prod.
Elpi Accumulate derive.eq 
  "eq-db (app[ {{prod}}, A, B ]) (app[{{prod_eq}}, A, FA, B, FB]) :-
    eq-db A FA, eq-db B FB.".

Elpi derive.eq list.
Elpi Accumulate derive.eq 
  "eq-db (app[ {{list}}, A ]) (app[{{list_eq}}, A, FA]) :-
    eq-db A FA.".

Inductive nat1 := O : nat1 | S (_ : nat1 * list nat1).

Inductive ForallPair A PA B PB : A * B -> Type := 
  K : forall (a : A) (b : B), PA a -> PB b -> ForallPair A PA B PB (a,b).

Inductive ForallList A PA : list A -> Type :=
  K1 : ForallList A PA (@nil A)
| K2 : forall x xs, PA x -> ForallList A PA xs -> ForallList A PA (x :: xs).

Lemma list_eqOK : forall A f l, ForallList A (axiom A f) l -> axiom (list A) (list_eq A f) l.
Proof.
move=> A f l; elim.
  case; try constructor => //.
move=> x xs IHx IHFxs IHxs [|y ys]; (try constructor) => //=.
case: (IHx y) => [ ->  | ].
  apply: reflect_eq_f2 => [[//]||]; try constructor=>//.
  apply: IHxs ys.
by move=> H; constructor 2=> [[H1 _]]; apply H.
Qed.

Lemma idF A P (x : A) : P x -> P x. Proof. auto. Qed.

Lemma ForallPairF A B p PA PB PA1 PB1 : 
  (forall x, PA x -> PA1 x) -> (forall x, PB x -> PB1 x) -> 
  ForallPair A PA B PB p -> ForallPair A PA1 B PB1 p.
Proof.
by move=> H1 H2; elim=> a b /H1 pa /H2 pb; constructor.
Qed.

Axiom prod_eqOK : forall A f B g p, ForallPair A (axiom A f) B (axiom B g) p -> axiom (A * B) (prod_eq A f B g) p.

Lemma nat1_indok :
  forall P : nat1 -> Type, (P O) -> (forall xl, ForallPair _ P _ (ForallList _  P) xl -> P (S xl)) ->
 forall x, P x.
Proof.
move=> P PO PS; refine (fix IH (x : nat1) : P x := match x with O => PO | S p => PS p _ end).
refine (match p with (p1, p2) => K _ _ _ _ p1 p2 _ _ end).
refine (IH _).
elim: p2. 
  apply: K1.
  by move=> y ys IHl; apply: K2.  
Qed.

Inductive nat2 (A : Type) := K3 : list (nat2 A) -> nat2 A.

Inductive Forallnat2 A (PA : A -> Type) : nat2 A -> Type := K3A : forall l, ForallList _ (Forallnat2 _ PA) l -> Forallnat2 A PA (K3 _ l).

Elpi derive.eq nat2.
Elpi Accumulate derive.eq 
  "eq-db (app[ {{nat2}}, A ]) (app[{{nat2_eq}}, A, FA]) :-
    eq-db A FA.".

Lemma nat2_indok :
  forall A (P : nat2 A -> Type), (forall xl : list (nat2 A), ForallList _  P xl -> P (K3 A xl)) ->
 forall x, P x.
Proof.
move=> A P IK.
refine (fix IH (x : nat2 A) : P x := match x with K3 _ xl => IK xl _ end).
elim: xl.
  apply: K1.
  by move=> ? ? ?; apply: K2.
Qed.

Inductive bad := K4 (_ : nat2 bad).

Elpi derive.eq bad.

Lemma bad_indok :
  forall P : bad -> Type, (forall xl, Forallnat2 _ P xl -> P (K4 xl)) ->
 forall x, P x.
Proof.
move=> P IK; refine (fix IH (x : bad) : P x := match x with K4 w => IK w _ end).
apply: (nat2_indok bad (Forallnat2 bad P)) => l Hl.
by apply: K3A.
Qed.

Elpi derive.eq nat1.
Elpi derive.projK nat1.
Lemma nat_eqOK x : axiom nat1 nat1_eq x.
Proof.
apply: (nat1_indok (axiom nat1 nat1_eq)).
- refine (fun m => _).
  refine match m with
         | O => _
         | S m1 => _
         end.
  + constructor 1. reflexivity.
  + constructor 2. refine (fun abs => _). discriminate.
- refine (fun n1 IH => _). 
  case => [ | m1 ].
  + constructor 2. refine (fun abs => _). discriminate.
  + rewrite /=.

   apply: reflect_eq_f1.
      (* refine (@f_equal _ _ (proj1S n1) _ _). *) by move=> [].
   apply: prod_eqOK.
   apply: ForallPairF (IH).
   apply: idF.
   apply: list_eqOK.
Qed.

Print prod_eq.
*)

Elpi Command derive.eqOK.
Elpi Accumulate File "derive/eqOK.elpi".
Elpi Accumulate "
  main [str I] :- !,
    coq-locate I T,
    if (T = indt GR) (derive-eqOK GR) usage.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.eqOK <inductive type name>"".
". 
