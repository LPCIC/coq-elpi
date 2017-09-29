From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import path choice fintype tuple finset bigop.

From elpi Require Import elpi.
Require Import test_param hrel ops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class refines X Y (R : X -> Y -> Type) x y : Type := Refines : R x y.
Arguments refines {_ _} R%rel _ _.

Lemma refines_apply
  {A B} {R : A -> B -> Type}
  {C D} {R' : C -> D -> Type} :
  forall (a : A) (b : B), refines R a b ->
  forall (c : A -> C) (d : B -> D), refines (R ==> R') c d ->
   refines R' (c a) (d b).
Proof. by move=> a b Rab c d; apply. Qed.

Cd "~/git/coq-elpi".
Elpi Run param "with-TC-param (param {{O}} X Y)".

Elpi Tactic coqeal " typecheck. ".
Elpi Accumulate File "coq-extra.elpi".
Elpi Accumulate File "coq-EAL.elpi".
Elpi Run coqeal " typecheck ".

Require Import ZArith pos.

Section positive_op.

Definition positive_of_pos (p : pos) : positive := Pos.of_nat (val p).
Definition pos_of_positive (p : positive) : pos := insubd pos1 (Pos.to_nat p).

Global Instance spec_positive   : Op.spec_of positive pos := pos_of_positive.
Global Instance implem_positive : Op.implem_of pos positive := positive_of_pos.
Global Instance one_positive    : Op.one_of positive := xH.
Global Instance add_positive    : Op.add_of positive := Pos.add.
Global Instance sub_positive    : Op.sub_of positive := Pos.sub.
Global Instance mul_positive    : Op.mul_of positive := Pos.mul.
Global Instance le_positive     : Op.leq_of positive := Pos.leb.
Global Instance lt_positive     : Op.lt_of positive  := Pos.ltb.
Global Instance eq_positive     : Op.eq_of positive  := Pos.eqb.
Global Instance exp_positive    : Op.exp_of positive positive := Pos.pow.
End positive_op.

Section positive_theory.

Local Open Scope rel_scope.

Lemma positive_of_posK : cancel positive_of_pos pos_of_positive.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
apply: val_inj; rewrite Nat2Pos.id ?insubdK -?topredE ?valP //.
by apply/eqP; rewrite -lt0n valP.
Qed.

Lemma to_natE : forall (p : positive), Pos.to_nat p = nat_of_pos p.
Proof.
by elim=> //= p <-;
rewrite ?Pos2Nat.inj_xI ?Pos2Nat.inj_xO NatTrec.trecE -mul2n.
Qed.

Lemma to_nat_gt0 p : 0 < Pos.to_nat p.
Proof.
by rewrite to_natE; elim: p => //= p; rewrite NatTrec.trecE double_gt0.
Qed.
Hint Resolve to_nat_gt0.

Lemma pos_of_positiveK : cancel pos_of_positive positive_of_pos.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
by rewrite val_insubd to_nat_gt0 Pos2Nat.id.
Qed.

Definition Rpos := fun_hrel pos_of_positive.

Lemma RposE (p : pos) (x : positive) :
  refines Rpos p x -> p = pos_of_positive x.
Proof. by []. Qed.

Lemma RposI (p : pos) (x : positive) :
  refines Rpos p x -> x = positive_of_pos p.
Proof. by move=> /RposE ->; rewrite pos_of_positiveK. Qed.

Global Instance Rpos_spec_pos_r x : refines Rpos (Op.spec x) x.
Proof. by []. Qed.

(* Global Instance Rpos_spec_pos_l : refines (Rpos ==> pos_R) spec_id spec. *)
(* Proof. *)
(*   rewrite refinesE=> x x'. *)
(*   rewrite -[Rpos]refinesE=> rx. *)
(*   rewrite [spec _]RposE [y in pos_of_positive y]RposI positive_of_posK /spec_id. *)
(*   exact: pos_Rxx. *)
(* Qed. *)

Global Instance Rpos_spec : refines (Rpos ==> Logic.eq) Op.spec_id Op.spec.
Proof. by rewrite []. Qed.

Global Instance Rpos_implem : refines (Logic.eq ==> Rpos) Op.implem_id implem.
Proof.
  rewrite refinesE=> _ x ->.
  case: x=> n ngt0.
  by rewrite /Rpos /fun_hrel positive_of_posK.
Qed.

Global Instance Rpos_1 : refines Rpos (pos1 : pos) (1%C : positive).
Proof. by rewrite !refinesE; apply: val_inj; rewrite /= insubdK. Qed.

Global Instance Rpos_add : refines (Rpos ==> Rpos ==> Rpos) add_pos +%C.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_add.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance Rpos_mul : refines (Rpos ==> Rpos ==> Rpos) mul_pos *%C.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_mul.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance Rpos_sub : refines (Rpos ==> Rpos ==> Rpos) sub_pos sub_op.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj; rewrite !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have [/leP h|/leP h] := (ltnP (Pos.to_nat y) (Pos.to_nat x)).
  by have := (Pos2Nat.inj_sub x y); rewrite Pos2Nat.inj_lt => ->.
rewrite /sub_op /sub_positive Pos.sub_le ?Pos2Nat.inj_le //.
by rewrite subn_gt0 !ltnNge; move/leP: h ->.
Qed.

Global Instance Rpos_leq : refines (Rpos ==> Rpos ==> bool_R) leq_pos Op.leq.
Proof.
  rewrite refinesE=> _ x <- _ y <-;
  rewrite /leq_op /le_positive /leq_pos !val_insubd.
  move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
  by case: (Pos.leb_spec0 _ _); move /Pos2Nat.inj_le /leP;
  [move ->|rewrite -eqbF_neg; move/eqP ->].
Qed.

Global Instance Rpos_lt : refines (Rpos ==> Rpos ==> bool_R) lt_pos Op.lt.
Proof.
rewrite refinesE => /= _ x <- _ y <-; rewrite /lt_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have -> : (Pos.to_nat x < Pos.to_nat y) = (x < y)%C.
  by apply/ltP/idP => [|h]; rewrite -Pos2Nat.inj_lt -Pos.ltb_lt.
exact: bool_Rxx.
Qed.

Global Instance Rpos_eq : refines (Rpos ==> Rpos ==> bool_R) eq_pos Op.eq.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /eq_op /eq_positive /eq_pos.
  case: (Pos.eqb_spec _ _)=> [->|h].
    by rewrite eqxx.
  suff H : (pos_of_positive x == pos_of_positive y) = false.
    by rewrite H.
  by apply/negP=> [/eqP /(can_inj pos_of_positiveK)].
Qed.

Lemma pos2nat_inj_exp x y : Pos.to_nat (x ^ y) = Pos.to_nat x ^ Pos.to_nat y.
Proof.
  have pos2nat_pow_xO a b
       (hab : Pos.to_nat (a ^ b) = Pos.to_nat a ^ Pos.to_nat b) :
    Pos.to_nat (a ^ b~0) = (Pos.to_nat a ^ Pos.to_nat b) ^ 2.
    by rewrite -Z2Nat.inj_pos Pos2Z.inj_pow Pos2Z.inj_xO Z.mul_comm Z.pow_mul_r
               // Z.pow_2_r -Pos2Z.inj_pow Z2Nat.inj_mul // Z2Nat.inj_pos multE
               hab mulnn.
  elim: y=> [y ihy|y ihy|].
      by rewrite Pos2Nat.inj_xI multE expnS [in _ ^ _]mulnC expnM Pos.xI_succ_xO
                 Pos.pow_succ_r Pos2Nat.inj_mul multE pos2nat_pow_xO.
    by rewrite Pos2Nat.inj_xO multE mulnC expnM pos2nat_pow_xO.
  by rewrite Pos2Nat.inj_1 expn1 Pos.pow_1_r.
Qed.

Global Instance Rpos_exp : refines (Rpos ==> Rpos ==> Rpos) exp_pos exp_op.
Proof.
  rewrite refinesE /exp_op /exp_positive=> _ x <- _ y <-.
  apply: val_inj.
  by rewrite !val_insubd expn_gt0 !to_nat_gt0 pos2nat_inj_exp.
Qed.

End positive_theory.

Typeclasses Opaque pos_of_positive positive_of_pos.
Global Opaque pos_of_positive positive_of_pos.

Section binnat_op.

Global Instance zero_N : Op.zero_of N := N.zero.
Global Instance one_N  : Op.one_of N  := N.one.
Global Instance add_N  : Op.add_of N  := N.add.

Definition succN (n : N) : N := (1 + n)%C.

Global Instance sub_N  : Op.sub_of N := N.sub.
Global Instance exp_N  : Op.exp_of N N := N.pow.
Global Instance mul_N  : Op.mul_of N := N.mul.
Global Instance div_N  : Op.div_of N := N.div.
Global Instance mod_N  : Op.mod_of N := N.modulo.
Global Instance eq_N   : Op.eq_of N  := N.eqb.
Global Instance leq_N  : Op.leq_of N := N.leb.
Global Instance lt_N   : Op.lt_of N  := N.ltb.

Global Instance cast_positive_N : Op.cast_of positive N := Npos.
Global Instance cast_N_positive : Op.cast_of N positive :=
  fun n => if n is Npos p then p else 1%C.

Global Instance spec_N : Op.spec_of N nat := nat_of_bin.
Global Instance implem_N : Op.implem_of nat N := bin_of_nat.

End binnat_op.

Section binnat_theory.

Local Open Scope rel_scope.

Definition Rnat : nat -> N -> Type := fun_hrel nat_of_bin.
Instance ref_Rnat : 'refinement Rnat.

Lemma RnatE (n : nat) (x : N) : refines_rec Rnat n x -> n = x.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_spec_r x : refines Rnat (spec x) x.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_spec : refines (Rnat ==> Logic.eq) Op.spec_id spec.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_implem : refines (Logic.eq ==> Rnat) Op.implem_id implem.
Proof.
rewrite !refinesE => x _ <-.
by rewrite /Rnat /fun_hrel /implem /implem_N bin_of_natK.
Qed.

Global Instance Rnat_0 : refines Rnat 0 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_1 : refines Rnat 1%nat 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_add : refines (Rnat ==> Rnat ==> Rnat) addn +%C.
Proof.
by rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel nat_of_add_bin.
Qed.

(* Hint Extern 999 (@refinement _ _ _) => *)
(*   (once lazymatch goal with |- ?g => idtac "trying " g; fail 1 end) *)
(*  : typeclass_instances. *)


Global Instance Rnat_S : refines (Rnat ==> Rnat) S succN.
Proof. by refines_abstrE; rewrite -add1n; apply/spec_refines. Qed.

Lemma nat_of_binK : forall x, N.of_nat (nat_of_bin x) = x.
Proof.
by case => //= p; apply: Nnat.N2Nat.inj; rewrite Nnat.Nat2N.id /= to_natE.
Qed.

Global Instance Rnat_sub : refines (Rnat ==> Rnat ==> Rnat) subn sub_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
by apply: Nnat.Nat2N.inj; rewrite Nnat.Nat2N.inj_sub !nat_of_binK.
Qed.

Global Instance Rnat_mul : refines (Rnat ==> Rnat ==> Rnat) muln mul_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
by rewrite /Rnat /fun_hrel /= nat_of_mul_bin.
Qed.

Global Instance Rnat_div_eucl :
  refines (Rnat ==> Rnat ==> prod_R Rnat Rnat) edivn N.div_eucl.
Proof.
rewrite refinesE /Rnat /fun_hrel=> _ x <- _ y <-.
rewrite edivn_def /=.
case: x=> [|x] /=; first by rewrite div0n mod0n.
case: y=> [|y] //=.
have hspec := N.pos_div_eucl_spec x (N.pos y).
have hrem := N.pos_div_eucl_remainder x (N.pos y).
destruct N.pos_div_eucl.
rewrite -[nat_of_pos _]/(nat_of_bin (N.pos _)) hspec /= {hspec}.
rewrite nat_of_add_bin nat_of_mul_bin.
have rem_lt_div : (n0 < N.pos y)%N.
  have pos_ne0 : N.pos y <> 0%num by [].
  have /= := hrem pos_ne0.
  rewrite /N.lt Nnat.N2Nat.inj_compare /= to_natE.
  move/nat_compare_lt/ltP.
  case: n0 {hrem}=> //= p.
  by rewrite to_natE.
rewrite modnMDl modn_small ?rem_lt_div // divnMDl /= -?to_natE ?to_nat_gt0 //.
by rewrite divn_small ?addn0 // ?to_natE.
Qed.

Global Instance Rnat_div : refines (Rnat ==> Rnat ==> Rnat) divn div_op.
Proof.  refines_abstrE; rewrite /divn; apply/spec_refines. Qed.

Global Instance Rnat_mod : refines (Rnat ==> Rnat ==> Rnat) modn mod_op.
Proof. by refines_abstrE; rewrite modn_def; apply/spec_refines. Qed.

Global Instance Rnat_exp : refines (Rnat ==> Rnat ==> Rnat) expn exp_op.
Proof.
  rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=.
  rewrite /exp_op /exp_N /N.pow.
  case: x y => [|x] [|y] //.
    rewrite exp0n //=; elim: y => //= p.
    by rewrite natTrecE double_gt0.
  have nat_of_binposE p : nat_of_bin (N.pos p) = Pos.to_nat p.
    elim: p=> [p ihp|p ihp|] /=; last (by rewrite Pos2Nat.inj_1);
      by rewrite ?(Pos2Nat.inj_xI, Pos2Nat.inj_xO) multE NatTrec.doubleE to_natE
                 mul2n.
  by rewrite !nat_of_binposE pos2nat_inj_exp.
Qed.

Global Instance Rnat_eq : refines (Rnat ==> Rnat ==> bool_R) eqtype.eq_op Op.eq.
Proof.
rewrite refinesE=> _ x <- _ y <-; rewrite /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq]; first by rewrite eqxx.
suff H : (nat_of_bin x == nat_of_bin y) = false by rewrite H.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Instance refines_spec_bool : 
  refines (bool_R ==> eq) Op.spec_id id.
Proof. by rewrite refinesE => ??[]. Qed.

Global Instance Rnat_leq : refines (Rnat ==> Rnat ==> bool_R) ssrnat.leq Op.leq.
Proof.
rewrite refinesE=> _ x <- _ y <-; rewrite /leq_op /leq_N /leq.
case: (N.leb_spec0 _ _)=> [/N.sub_0_le|] xBy.
  by rewrite [_ == _](coqeal unify) [sub_op _ _]xBy.
suff H : (nat_of_bin x - nat_of_bin y == 0) = false.
  by rewrite /(_ <= _)%N H.
apply/negP=> /eqP; rewrite [x - y]RnatE [0]RnatE.
by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

Global Instance Rnat_lt : refines (Rnat ==> Rnat ==> bool_R) ltn lt_op.
Proof.
refines_abstr; rewrite refinesE /ltn /= ltnNge; apply/eq_spec_refines.
by rewrite /lt_op /lt_N N.ltb_antisym.
Qed.

Global Instance Rnat_cast_positive_N :
  refines (Rpos ==> Rnat) val (cast : positive -> N).
Proof.
  rewrite refinesE /cast /Rnat /fun_hrel => x x' rx.
  by rewrite [x]RposE val_insubd to_nat_gt0 to_natE.
Qed.

Global Instance Rnat_cast_N_positive :
  refines (Rnat ==> Rpos) (insubd pos1) (cast : N -> positive).
Proof.
  rewrite refinesE=> x x' rx; rewrite [x]RnatE.
  case: x' {x rx} => [|p] /=; last by rewrite -to_natE.
  rewrite /insubd insubF //= /cast.
  by apply (@spec_refinesP _ _ _ _ _ _ _ _ _).
Qed.

End binnat_theory.

Typeclasses Opaque nat_of_bin bin_of_nat.
Global Opaque nat_of_bin bin_of_nat.

Section test.

Instance : 'refinement Rnat.

Lemma test : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof.
by rewrite [X in X = _](coqeal unify); reflexivity.
Qed.

Lemma test' : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by apply/eqP; rewrite [_ == _](coqeal unify). Qed.

End test.


Section CoqEAL.

Context (N : Type).
Context (R : nat -> N -> Type).
Context (zero one : N).
Context (add : N -> N -> N).
Context (N_of_bool : bool -> N).

Context {Rzero : refines R 0 zero}.
Context {Rone : refines R 1 one}.
Context {Radd : refines (R ==> R ==> R)%rel addn add}.

Context {Rfrombool : forall b, refines R (nat_of_bool b) (N_of_bool b)}.

Lemma test_refines0 : { x : _ & refines R 1 x}.
Proof.
  eexists.
  elpi coqeal; shelve_unifiable.
Abort.

Lemma test_refines0 : { x : _ & refines R true x}.
Proof.
  eexists.
  elpi coqeal; shelve_unifiable.
Qed.


Lemma test_refines1 : { x : _ & refines (R ==> R) (addn 1) x}.
Proof.
  eexists.
  elpi coqeal; shelve_unifiable.
Qed.

Lemma test_refines2 : { x : _ & refines R (addn 1 0) x}.
Proof.
  eexists.
  elpi coqeal; shelve_unifiable.
Qed.

Lemma test_refines_big : { x : N & refines R (0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + true)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1))))))))%nat x}.
Proof.
  eexists.
  Time elpi coqeal; shelve_unifiable.
Show Proof.
Qed.

Elpi Run coqeal "
  coq-locate ""nat_ind"" (const GR),
  coq-env-typeof-gr GR (prod N _ _),
  $term_to_string N S,
  S' is S ^ ""1"",
  coq-say S'.
".

End CoqEAL.
