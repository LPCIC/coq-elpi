From Corelib Require Import ssreflect ssrbool.
From Corelib Require Export PrimString Uint63Axioms PrimStringAxioms.

Register PrimString.string as elpi.pstring.

Definition eqb (s1 s2 : PrimString.string) :=
  match PrimString.compare s1 s2 with Eq => true | _ => false end.

Register eqb as elpi.pstring_eqb.

Lemma compare_Eq_refl (s : string) : compare s s = Eq.
Proof.
  rewrite PrimStringAxioms.compare_spec.
  elim: (to_list s) => //= x xs ->.
  rewrite Uint63Axioms.compare_def_spec /compare_def eqb_refl.
  suff: ltb x x = false by move->.
  have [+ _] := ltb_spec x x.
  by case: ltb => // /(_ isT); case: (to_Z x) => //=; elim.
Qed.
Lemma compare_Eq_correct (s1 s2 : string) :
  compare s1 s2 = Eq -> s1 = s2.
Proof.
  move=> E; rewrite -[s1]of_to_list -[s2]of_to_list; congr (of_list _).
  move: E; rewrite compare_spec.
  elim: (to_list s1) (to_list s2) => [[]//|x xs IH [|y ys] //=].
  rewrite Uint63Axioms.compare_def_spec /compare_def.
  move: (eqb_correct x y); case: PrimInt63.eqb => [/(_ isT)->|_].
    suff: ltb y y = false by move=> -> /IH ->.
    have [+ _] := ltb_spec y y.
    by case: ltb => // /(_ isT); case: (to_Z y) => //=; elim.
  by case: ltb.
Qed.
Lemma compare_ok (s1 s2 : string) : compare s1 s2 = Eq <-> s1 = s2.
Proof. split; [apply compare_Eq_correct|intros []; apply compare_Eq_refl]. Qed.
