From elpi.core Require Import ssreflect ssrfun ssrbool.
From elpi Require Import elpi.
From elpi.apps Require Import derive.
From elpi.apps.derive Require Import induction param1_functor param1_trivial eqb_core_defs tag fields eqb.

From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "eqbcorrect.elpi" as eqbcorrect.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Module Export exports.
Export ssreflect ssrbool eqb_core_defs. (* go ask the ltac gurus... *)
Ltac solver_regular_or_dependent :=
  match reverse goal with 
  | View : @eqb_correct_on _ ?f ?y |- is_true (?f ?y ?x && _) -> _ =>
      case/andP => /View => ? {View}; subst x
  end.

Ltac solver_irrelevant :=
  match goal with
  | p1 : ?x = true , p2 : ?x = true |- _ =>
     let top := fresh "x" in
     have top := @eqb_core_defs.UIP_dec bool eqb_core_defs.bool_dec _ _ p1 p2;
     subst p1
  end.

Ltac eqb_correct_on__solver :=
  let x := fresh "x" in case=> [^ x] /=;
  by repeat (solver_regular_or_dependent || solver_irrelevant).

Ltac eqb_refl_on__solver :=
  by rewrite /eqb_fields_refl_on /=;
  repeat ((apply /andP; split) || reflexivity || assumption).
End exports.

From elpi.core Require Uint63Axioms.

Lemma uint63_eqb_correct i : eqb_correct_on PrimInt63.eqb i.
Proof. exact: Uint63Axioms.eqb_correct. Qed.

Lemma uint63_eqb_refl i : eqb_refl_on PrimInt63.eqb i.
Proof. exact: Uint63Axioms.eqb_refl. Qed.

From elpi.core Require PrimString PrimStringAxioms.

Lemma pstring_eqb_correct i : eqb_correct_on PrimString.eqb i.
Proof.
   move=> j; rewrite /PrimString.eqb; have [] := PrimStringAxioms.compare_ok i j.
   by case: PrimString.compare => // /(_ erefl).
Qed.

Lemma pstring_eqb_refl i : eqb_refl_on PrimString.eqb i.
Proof.
   rewrite /PrimString.eqb /eqb_refl_on; have [] := PrimStringAxioms.compare_ok i i.
   by case: PrimString.compare => // _ /(_ erefl).
Qed.

Elpi Db derive.eqbcorrect.db lp:{{

  pred eqcorrect-for
    o:gref,
    o:constant, % correct
    o:constant. % reflexive
  
  eqcorrect-for {{:gref PrimInt63.int }} C R :-
    {{:gref uint63_eqb_correct}} = const C,
    {{:gref uint63_eqb_refl}} = const R.

  :index(2)
  pred correct-lemma-for i:term, o:term.
  correct-lemma-for {{ PrimInt63.int }} {{ @uint63_eqb_correct }}.
  correct-lemma-for {{ PrimString.string }} {{ @pstring_eqb_correct }}.

  :index(2)
  pred refl-lemma-for i:term, o:term.
  refl-lemma-for {{ PrimInt63.int }} {{ @uint63_eqb_refl }}.
  refl-lemma-for {{ PrimString.string }} {{ @pstring_eqb_refl }}.

}}.


(* standalone *)
Elpi Command derive.eqbcorrect.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File eqbcorrect.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate File eqType.
Elpi Accumulate Db derive.param1.db.

Elpi Accumulate lp:{{
  main [str I] :- !, 
    coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.eqbcorrect.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqbcorrect <inductive name>".

}}.

(* hook into derive *)
Elpi Accumulate derive File eqbcorrect.
Elpi Accumulate derive Db derive.eqbcorrect.db.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "eqbcorrect" "eqb".
dep1 "eqbcorrect" "induction".
dep1 "eqbcorrect" "param1_inhab".
dep1 "eqbcorrect_alias" "eqb_alias".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eqbcorrect" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "eqbcorrect" (derive.eqbcorrect.main (indt T) Prefix) (eqcorrect-for (indt T) _ _)).
derivation (const C) Prefix ff (derive "eqbcorrect_alias" (derive.eqbcorrect.main (const C) Prefix) (eqcorrect-for (const C) _ _)).

}}.
