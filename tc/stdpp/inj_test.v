From stdpp Require Import base.
Require Import Lia.
From elpi Require Import elpi.

(* Print Instances Inj. *)
Check (_ : forall A B C R1 R2 R3 f g _ _, Inj R1 R3 (compose g f)).

Lemma injCompose: forall A B C (f : A -> B) (g : B -> C), 
Inj eq eq f -> Inj eq eq g -> Inj eq eq (fun a => g (f a)).
Proof.
  intros; apply (compose_inj eq eq); easy.
Qed.

Definition g x := x + 1.
Definition f (x: nat) := x.

Lemma isInjg : Inj eq eq g.
Proof.
  red; unfold g; destruct x, y; lia.
Qed.

Lemma isInjf : Inj eq eq f.
Proof.
  red; unfold f; intuition.
Qed.

