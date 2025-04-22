(* Generates soudness proofs given correctness and reflexivity.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi.apps.derive Require Import eqb_core_defs.
From elpi.apps.derive Require Import tag eqType_ast fields eqb eqbcorrect derive.

From elpi.apps.derive.elpi Extra Dependency "eqbOK.elpi" as eqbOK.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Elpi Db derive.eqbOK.db lp:{{

  pred eqbok-for o:gref, o:constant.

}}.
#[superglobal] Elpi Accumulate derive.eqbOK.db File derive.lib.

Lemma reflect_dec : forall a b, (forall x y : a, reflect (x=y) (b x y)) -> forall x y : a, {x=y}+{x<>y}.
Proof.
 intros A b H x y.
 destruct (H x y); auto.
Defined.

Definition eqb_of_dec : forall a (H : forall x y : a, {x=y}+{x<>y}), a -> a -> bool :=
  fun a H x y => (match H x y with left _ => true | right _ => false end).

Definition dec_reflect : forall a (H : forall x y : a, {x=y}+{x<>y}), forall x y : a, reflect (x=y) (eqb_of_dec a H x y) :=
  fun a H x y => match H x y as H return reflect (x=y) (match H with left _ => true | right _ => false end) with left p => ReflectT _ p | right p => ReflectF _ p end.

(* standalone *)
Elpi Command derive.eqbOK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.eqbOK.db.
Elpi Accumulate File eqbOK.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{
  main [str I] :- !, 
    coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.eqbOK.main GR Prefix _.

  main _ :- usage.

  usage :- coq.error "Usage: derive.eqbOK <inductive name/alias>".

}}.


(* hook into derive  *)
Elpi Accumulate derive File eqbOK.
Elpi Accumulate derive Db derive.eqbOK.db.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "eqbOK" "eqbcorrect".
dep1 "eqbOK_alias" "eqbcorrect_alias".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eqbOK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "eqbOK" (derive.eqbOK.main (indt T) Prefix) (eqbok-for (indt T) _)).
derivation (const T) Prefix ff (derive "eqbOK_alias" (derive.eqbOK.main (const T) Prefix) (eqbok-for (const T) _)).

}}.


Elpi Command derive.eqbOK.register_axiom.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{
   main [str Type, str IsT, str IsTinhab, str Eqb, str Correct, str Refl] :- !,
     coq.locate Type GrType,
     coq.locate IsT GRisT,
     coq.locate IsTinhab GRisTinhab,
     coq.locate Eqb GrEqb,
     coq.locate Correct GrCorrect,
     coq.locate Refl GrRefl,
     GrRefl = const R,
     GrCorrect = const C,
     coq.elpi.accumulate _ "derive.eqb.db" (clause _ _ (eqb-done GrType)),
     coq.elpi.accumulate _ "derive.eqb.db" (clause _ _ (eqb-for (global GrType) (global GrType) (global GrEqb))),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (eqcorrect-for GrType C R)),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (correct-lemma-for (global GrType) (global GrCorrect))),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (refl-lemma-for (global GrType) (global GrRefl))),
     coq.elpi.accumulate _ "derive.eqType.db" (clause _ _ (eqType GrType eqb.axiom)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ _ (reali-done GrType)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ (before "reali:fail") (reali (global GrType) (global GRisT) :- !)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ (before "realiR:fail") (realiR (global GrType) (global GRisT) :- !)),
     coq.elpi.accumulate _ "derive.param1.trivial.db" (clause _ _ (param1-inhab-db (global GRisT) (global GRisTinhab))).
  main _ :- coq.error "usage: derive.eqbOK.register_axiom T is_T is_T_inhab eqb eqb_correct eqb_refl.".
}}.
Elpi Export derive.eqbOK.register_axiom.
