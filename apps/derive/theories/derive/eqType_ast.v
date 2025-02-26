From elpi Require Import elpi.
From elpi.core Require Import PrimInt63 PrimFloat PrimString.
From elpi.apps Require Import derive.

From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Elpi Db derive.eqType.db lp:{{

kind eqb.arguments type.
kind eqb.trm type.
kind eqb.eqType type.
kind eqb.constructor type.

type eqb.app    gref -> eqb.trm -> list eqb.trm -> eqb.trm.
type eqb.global gref -> eqb.trm.

type eqb.regular    eqb.trm -> eqb.arguments -> eqb.arguments.
type eqb.irrelevant eqb.trm -> eqb.arguments -> eqb.arguments.
type eqb.dependent  eqb.trm -> (eqb.trm -> eqb.arguments) -> eqb.arguments.
type eqb.stop       eqb.trm -> eqb.arguments.

type eqb.type-param  (eqb.trm -> eqb.eqType) -> eqb.eqType.
type eqb.value-param eqb.trm -> (eqb.trm -> eqb.eqType) -> eqb.eqType.
type eqb.inductive   inductive -> (eqb.trm -> list eqb.constructor) -> eqb.eqType.
type eqb.axiom       eqb.eqType.

type eqb.constructor constructor -> eqb.arguments -> eqb.constructor.

pred eqType i:gref, o:eqb.eqType.
eqType {{:gref PrimInt63.int }} eqb.axiom :- !.
eqType {{:gref lib:elpi.pstring }} eqb.axiom :- !.

}}.

Definition arrow T1 T2 := T1 -> T2.
Register arrow as elpi.derive.arrow.
Definition apply {T1 T2} (f : T1 -> T2) x := f x.
Register apply as elpi.derive.apply.

(* standalone *)
Elpi Command derive.eqType.ast.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{

main [str S] :-
  std.assert! (coq.locate S (indt I)) "derive.eqType.ast: not an inductive",
  derive.eqType.ast.main I _.

}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.eqType.db.
Elpi Accumulate derive File eqType.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eqType_ast" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) _ ff (derive "eqType_ast" (derive.eqType.ast.main T) (eqType (indt T) _)).

}}.
