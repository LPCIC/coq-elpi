From elpi Require Import derive.param1 derive.invert derive.induction derive.idx2inv.

Elpi derive.param1 list.
Elpi derive.invert listR.

Elpi derive.param1 listR.
Elpi derive.param1P listR.
Elpi derive.induction listR.

Require Import ssreflect.
Lemma list_inv A PA l :  listR A PA l -> listR_inv A PA l.
Proof.
elim/listR_induction.
  by apply: (nilR_inv A PA nil eq_refl).
move=> x _ px _ xs _ pxs IH.
apply: (consR_inv A PA (x :: xs)%list x px xs xs eq_refl IH eq_refl).
Qed.


Elpi derive.param1 eq.

Lemma eqrP A PA (x y : A) px py (e : x = y) : eqR A PA x px y py e.
case: _ / e in py *.
constructor.

Elpi derive.param1P eqR.
Elpi derive.param1 nat.
Elpi derive.param1 listR_inv.
Elpi derive.induction listR_invR.

Elpi derive.param1P listR_inv.
STOP.

Inductive vect A i : Type := 
 vn : 0 = i -> vect A i |
 vc : forall k, A -> vect A k -> S k = i -> vect A i.
Print eqR.
Inductive vectR A (PA : A -> Type) (i : nat) (iR : natR i) : vect A i -> Type :=
  vnR : forall (e : 0 = i), eqR nat natR 0 OR i iR e -> vectR A PA i iR (vn A i e)
| vcR : forall k (kR : natR k) a (pa : PA a) (v : vect A k) (IH : vectR A PA k kR v),
           forall (e : S k = i), 
           eqR nat natR (S k) (SR k kR) i iR e -> vectR A PA i iR (vc A i k a v e).

 


Print eqR.
Print listRR.
Inductive listR_invR A PA PA1 PPA1 l Pl r


Elpi derive.param1 listR_inv.
Elpi derive.param1P listR.
Elpi derive.induction listR.
*)

Lemma inv_list A PA l : listR_inv A PA l -> listR A PA l.
Proof.
elim.
  by move=> ? <-; apply: (nilR A PA).
move=> _ x px w xs E pxs IH <-.
rewrite E; apply: (consR A PA x px xs IH).
Qed.


Inductive t := Node : list t -> t.

From elpi Require Import  derive.map.
Elpi derive.param1 list.
Elpi derive.param1 t.
Elpi derive.invert listR.
Elpi derive.invert tR.
Elpi derive.param1P listR.
Elpi derive.map listR.
Elpi derive.induction list.
Elpi derive.induction t.

Require Import ssreflect.
Check list_induction.


Lemma list_inv A PA l :  listR A PA l -> listR_inv A PA l.
Proof.
elim/list_induction: l.
  by constructor.
move=> a _ l IH I.
case : {-2}_ / I (eq_refl (a :: l)%list).
  by move=> _; apply: nilR_inv.
move=> a0 pa l0 pl [_ El0].
apply: (consR_inv A PA (a0 :: l0)%list a0 pa l0 l El0 (IH _) eq_refl).
by rewrite -El0.
Qed.

Lemma inv_list A PA l :  listR_inv A PA l -> listR A PA l.
Proof.
elim/list_induction: l.
  by constructor.
move=> a _ l IH I.
case : I.
  by discriminate.
move=> a0 pa l0 l1 E12 Pl1 [E1 E2].
apply: (consR A PA a _ l _).
  by rewrite -E1; apply: pa.
by apply: IH; rewrite -E2 E12; apply: Pl1.
Qed.

Lemma l_ind A PA P : P (@nil A) -> (forall x (px : PA x) xs (pxs : listR A PA xs), P xs -> P (x :: xs)%list) ->  forall l, (listR A PA l) -> P l.
Proof.
move=> P0 PS; elim/list_induction.
  by move=> _; apply: P0.
move=> x _ xs IH; case/list_inv; first by discriminate.
move=> y Py ys w Dw /inv_list Pw [Ey Eys].
apply: PS.
  rewrite -Ey; by apply: Py.
  by rewrite -Eys Dw; apply: Pw.
by apply: IH; rewrite -Eys Dw.
Qed.


Lemma l_indxx A PA P : P (@nil A) -> (forall x (px : PA x) xs (pxs : listR A PA xs), P xs -> P (x :: xs)%list) ->  forall l, (listR A PA l) -> P l.
Proof.
move=> P0 PS; elim/list_induction.
  by [].
move=> x _ xs IH H; case: {-2}_ / H (eq_refl (x::xs)%list); first by discriminate.
move=> y Py ys Pys [Ey Eys].
apply: PS.
  by apply: Py.
  by apply: Pys.
by rewrite Eys; apply: IH; rewrite -Eys; apply: Pys.
Qed.
(*
Lemma l_ind_inv A PA P : P (@nil A) -> (forall x (px : PA x) xs (pxs : listR_inv A PA xs), P xs -> P (x :: xs)%list) ->  forall l, (listR_inv A PA l) -> P l.
Proof.
move=> PO PS l /inv_list.
by apply: l_ind => // x px xs pxs Pxs; apply: PS => //; apply/list_inv.
Qed.
*)


Lemma listRext A P Q (H : forall l, listR A P l -> listR A Q l) l : listR A (fun x => P x -> Q x) l.
Proof.
elim: l.
  constructor.
move=> x xs IH; constructor.
  move=> px; case: {-2}_ / (H (x :: nil)%list) (eq_refl (x :: nil)%list).
    constructor=> //; constructor.
    discriminate.
  by move=> y Qy ?? [<- _].
by apply: IH.
Qed.

Lemma listRext1 A P Q (H : forall l, listR A P l -> listR A Q l) l : listR A (fun x => P x -> Q x) l.
Proof.
elim: l.
  constructor.
move=> x xs IH; constructor.
  move=> px; case: (list_inv _ _ _ (H (x :: nil)%list _)).
    constructor=> //; constructor.
    discriminate.
  by move=> y Qy ???? [<- _].
by apply: IH.
Qed.

Lemma listRMP A P Q l : listR A P l -> listR A (fun x => P x -> Q x) l -> listR A Q l.
Proof.
elim/l_ind.
  by constructor.
move=> x px xs pxs IH /list_inv [//| y pqy l1 l2 E12 /inv_list H [E1 E2] ].
apply: consR (x) _ (xs) _.
  by rewrite -E1; apply: pqy; rewrite E1; apply: px.
by apply: IH; rewrite -E2 E12; apply: H.
Qed.

Lemma t_inv t : tR t -> tR_inv t.
Proof.
elim/t_induction: t => l IH pl.
case : {-2}_ / pl (eq_refl (Node l)).
move=> x px [E].
apply: NodeR_inv (Node x) (x) _ eq_refl. 
rewrite E.
apply: listRMP _ IH.
rewrite -E.
apply: px.
Qed.

Lemma inv_t t : tR_inv t -> tR t.
Proof.
elim/t_induction: t => l IH pl.
case : pl.
move=> x px [E].
apply: NodeR.
apply: listRMP _ IH.
rewrite -E.
apply: px.
Qed.
