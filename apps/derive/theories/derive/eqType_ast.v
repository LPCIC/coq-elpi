From elpi Require Import elpi.
From Corelib Require Import PrimInt63 PrimFloat.
From elpi.apps.derive Require Import PrimStringEqb.
From elpi.apps Require Export derive.

From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Elpi Db derive.eqType.db lp:{{

data eqb.arguments.
data eqb.trm.
data eqb.eqType.
data eqb.constructor.

symb eqb.app    : gref -> eqb.trm -> list eqb.trm -> eqb.trm.
symb eqb.global : gref -> eqb.trm.

symb eqb.regular    : eqb.trm -> eqb.arguments -> eqb.arguments.
symb eqb.irrelevant : eqb.trm -> eqb.arguments -> eqb.arguments.
symb eqb.dependent  : eqb.trm -> (eqb.trm -> eqb.arguments) -> eqb.arguments.
symb eqb.stop       : eqb.trm -> eqb.arguments.

symb eqb.type-param  : (eqb.trm -> eqb.eqType) -> eqb.eqType.
symb eqb.value-param : eqb.trm -> (eqb.trm -> eqb.eqType) -> eqb.eqType.
symb eqb.inductive   : inductive -> (eqb.trm -> list eqb.constructor) -> eqb.eqType.
symb eqb.axiom       : eqb.eqType.

symb eqb.constructor : constructor -> eqb.arguments -> eqb.constructor.

pred eqType gref -> eqb.eqType.
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
