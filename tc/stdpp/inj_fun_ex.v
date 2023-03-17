From stdpp Require Export base.
Require Import Lia.

Generalizable All Variables.

Definition g x := x + 1.
Definition f (x: nat) := x.

Axiom eq1 : relation nat.
Axiom eq2 : relation nat.
Axiom eq3 : relation nat.

Lemma isInjg : Inj eq3 eq1 g. Admitted.

Lemma isInjf : Inj eq1 eq3 f. Admitted.

Lemma isInjf_old : Inj eq1 eq2 f. Admitted.
Lemma isInjg_old : Inj eq2 eq3 g. Admitted.

Lemma isInjinr {A B}: Inj eq eq (@inr A B).
Proof.
  red; intros.
  injection H.
  easy.
Qed.

Lemma isInjf_eq : Inj eq eq f.
Proof. red; intuition. Defined.

Lemma isInjg_eq : Inj eq eq g.
Proof. red; unfold g; intros [| x] [|y]; lia. Defined.

Global Existing Instance isInjf_eq.
Global Existing Instance isInjg_eq.
Global Existing Instance isInjf.
Global Existing Instance isInjg.
Global Existing Instance isInjf_old.
Global Existing Instance isInjg_old.
