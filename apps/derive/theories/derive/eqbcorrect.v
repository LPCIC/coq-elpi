From Coq Require Import ssreflect ssrfun ssrbool Eqdep_dec.
From elpi Require Import elpi.
From elpi.apps.derive Require Import induction param1_functor param1_trivial eqb_core_defs tag fields eqb.

From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive Extra Dependency "eqbcorrect.elpi" as eqbcorrect.

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
     have top := @Eqdep_dec.UIP_dec bool Bool.bool_dec _ _ p1 p2;
     subst p1
  end.

Ltac eqb_correct_on__solver :=
  let x := fresh "x" in case=> [^ x] /=;
  by repeat (solver_regular_or_dependent || solver_irrelevant).

Ltac eqb_refl_on__solver :=
  by rewrite /eqb_fields_refl_on /=;
  repeat ((apply /andP; split) || reflexivity || assumption).
      
Elpi Command derive.eqbcorrect.
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
  main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.eqbcorrect.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.eqbcorrect.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqbcorrect <inductive name> [<prefix>]".

}}.
Elpi Typecheck.