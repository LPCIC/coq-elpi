From elpi.apps.tc.tests Require Import stdppInj.
Elpi TC_solver. Set TimeRefine. Set TimeTC. Set Debug "elpitime". 
Elpi Override TC TC_solver All.

About h.
About trans_co_eq_inv_impl_morphism.

Goal Inj eq eq
  (((f ∘ f) ∘ (f ∘ f)) ∘ ((f ∘ f) ∘ (f ∘ f))). 
Time apply _. Show Proof. Qed.

Elpi Accumulate TC_solver lp:{{
  :after "0"
  tc-Inj A B RA RB {{@compose lp:A lp:B lp:C lp:LC lp:RC}} Sol :- 
    LC = RC, !,
    tc-Inj A B RA RB LC Sol1, 
    coq.typecheck LC TLC ok,
    coq.typecheck Sol1 TSol1 ok,
    Sol = {{
      let sol : lp:TSol1 := lp:Sol1 in 
      let fl : lp:TLC := lp:LC in 
      @compose_inj lp:A lp:B lp:C lp:RA lp:RA lp:RB fl fl sol sol}}.
}}.


Goal Inj eq eq
  (((f ∘ f) ∘ (f ∘ f)) ∘ ((f ∘ f) ∘ (f ∘ f))). 
Time apply _. Show Proof. Qed.

