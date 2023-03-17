From stdpp Require Import base sets.

Context `{FinSet EX XS}.
Context `{FinSet EY YS}.
Context `{FinSet EE ES}.

(* 
  If f : X -> Y is injective and A & B are both subsets of X then f(A inter B) = f(A) inter f(B)
*)
Lemma subset: forall (X: XS) (Y: YS) A B (f: XS -> YS), A ⊆ X -> B ⊆ X -> 
forall a b c (E: ES) (F: ES), c ∈ (A ∩ B) -> a ∈ A -> b ∈ B -> f c ∈ E -> f a ∈ F -> f b ∈ F -> E ⊆ F.  
True.
Proof.
  intros.
  intros; apply (compose_inj eq eq); easy.
Qed.