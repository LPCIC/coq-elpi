Require Import elpi. (*	elpi.derive.eq elpi.derive.projK elpi.derive.isK elpi.derive.param1.

Require Import Bool List ssreflect.

Elpi derive.param1 prod andR.
Elpi derive.param1 list listR.

Inductive nat1rec T L : Type := O : nat1rec T L | S (_ : T * L T).
Elpi derive.param1 nat1rec nat1recR.
Elpi derive.param1 nat1rec_rect nat1rec_rectR.

Print nat1recR_rect.


Check (fun P => nat1recR_rect _ P _ listR).


Elpi derive.param1 nat1 nat1R.

Check fun Pred => 
  nat1R_rect _ Pred _ listR.


Inductive nat1 : Type := O : nat1 | S (_ : nat1 * list nat1).

Elpi derive.param1 nat1 nat1R.
Print nat1R_ind. Print nat1R.

Lemma nat1RP : forall n : nat1, nat1R n.
Proof.
fix IH 1 => n.
refine match n as w in nat1 return nat1R w
       with O => _ | S x => _ end.
refine nat1R_O.
refine (nat1R_S _ _).
case: x; constructor.
  exact: IH.
elim: b; constructor => //.
Qed.

Definition nat1R_ind_fixed
: forall P : nat1 -> Prop,
       P O ->
       (forall H : nat1 * list nat1,
        andR nat1 P (list nat1) (listR nat1 P) H -> P (S H)) ->
       forall s : nat1, nat1R s -> P s.
Proof.

move=> P fO fS; fix IH 2 => n nr.
refine 
match nr in nat1R m return P m with
| nat1R_O => fO
| nat1R_S s Ps => fS s _
end.
(* functoriality on Ps *)
Admitted.

Definition nat1_induction P PO PS x :=
  nat1R_ind_fixed P PO PS x (nat1RP x).


About nat1_induction.



move=> n; elim: n.

refine
match Ps in andR _ _ _ _ a return andR nat1 P (plist nat1) (plistR nat1 P) a with
| andR_conj _ _ _ _ a Pa b Pb => andR_conj _ _ _ _ _ _ _ _
end.
  refine (IH a Pa).
elim: Pb.


refine
match Pb in plistR _ _ a return plistR nat1 P a with
| andR_conj _ _ _ _ a Pa b Pb => 
| 
end.


 fun (P : nat1 -> Prop) (fO : P O)
  (fS : forall H : nat1 /\ plist nat1,
        andR nat1 P (plist nat1) (plistR nat1 P) H -> P (S H))
  (s : nat1) (n : nat1R s) =>
fix rec n :=
match n in (nat1R s0) return (P s0) with
| nat1R_O => fO
| nat1R_S x x0 => fS x x0
end.

About nat1R_ind. Print andR.   Print plistR.


Definition axiom T eqb x := forall (y : T), reflect (x = y) (eqb x y).

Lemma reflect_eq_f1 T rT (f : T -> rT) x y (inj_f : forall x y, f x = f y -> x = y) b :
  reflect (x = y) b -> reflect (f x = f y) b.
Proof.
case=> [ -> | abs ]; first by constructor 1.
by constructor 2 => /inj_f .
Qed.

(*
Lemma reflect_eq_f2 T rT (f : T -> rT) x y 
   (inj_f : f x = f y -> x = y) b1 b2 :
  reflect (f = f) b1 ->
  reflect (x = y) b2 -> reflect (f x = f y) (b1 && b2).
Proof.
by case=> [ E1 | abs1 ]; case=> [ -> | abs2 ]; constructor => //; try move/inj_f.
Qed.
*)
Lemma reflect_eq_f2 T S rT (f : T -> S -> rT) x y a b 
   (inj_f1 : forall x y a b, f x a = f y b -> x = y)
   (inj_f2 : forall x y a b, f x a = f y b -> a = b)
    b1 b2 :
  reflect (x = y) b1 ->
  reflect (a = b) b2 -> reflect (f x a = f y b) (b1 && b2).
Proof.
case=> [ -> | abs1 ]; case=> [ -> | abs2 ]; constructor => //; first [ by move/inj_f1 | by move/inj_f2 ].
Qed.

Elpi derive.eq prod. (* XXX broken: Elpi Print derive.eq. *)
Elpi derive.param1 prod prod_Forall.
Elpi derive.projK prod.

Lemma prod_eqOK : forall A f B g p,
  prod_Forall A (axiom A f) B (axiom B g) p ->
    axiom (A * B) (prod_eq A f B g) p.
Proof.
move=> A f B g p; elim=> a Ha b Hb.
case=> x y /=.
apply: reflect_eq_f2 => // d1 ? d2 ? H.
  apply: (f_equal (proj1pair _ _ d1) H).
apply: (f_equal (proj2pair _ _ d1 d2) H).
Qed.

Elpi derive.eq list.
Elpi derive.param1 list list_Forall.
Elpi derive.projK list.
Elpi derive.isK list.

(*
Lemma list_eqOK : forall A f l, list_Forall A (axiom A f) l -> axiom (list A) (list_eq A f) l.
Proof.
move=> A f l; elim => [|x Hx xs Pxs Hxs].
  case=> [ | y ys].
    constructor 1; reflexivity.
  by constructor 2; move/(f_equal (isnil _)).
case=> [ | y ys].
  by constructor 2; move/(f_equal (iscons _)).
apply: reflect_eq_f2 Hx Hxs => //.
  apply: (f_equal (proj1pair _ _ d1) H).
apply: (f_equal (proj2pair _ _ d1 d2) H).

case: (Px y) => [ ->  | ].
  apply: reflect_eq_f2 => [[//]||]; try constructor=>//.
  apply: IHxs ys.
by move=> H; constructor 2=> [[H1 _]]; apply H.
Qed.
*)


Lemma idF A P (x : A) : P x -> P x. Proof. auto. Qed.

Lemma ForallPairF A B p PA PB PA1 PB1 : 
  (forall x, PA x -> PA1 x) -> (forall x, PB x -> PB1 x) -> 
  ForallPair A PA B PB p -> ForallPair A PA1 B PB1 p.
Proof.
by move=> H1 H2; elim=> a b /H1 pa /H2 pb; constructor.
Qed.



Lemma nat1_indok :
  forall P : nat1 -> Type, (P O) -> 
    (forall xl, ForallPair _ P _ (ForallList _  P) xl -> P (S xl)) ->
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
  forall A (P : nat2 A -> Type), (
forall xl : list (nat2 A), ForallList _  P xl -> P (K3 A xl)) ->
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
