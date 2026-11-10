From elpi Require Import elpi.
From Corelib Require Import PrimInt63 PrimFloat.
From elpi.apps.derive Require Import PrimStringEqb.
From elpi.apps Require Export derive.

From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "eqType.db.elpi" as eqTypedb.

Elpi Db derive.eqType.db lp:{{ accumulate "elpi.apps.derive.elpi/eqType.db". }}.

Definition arrow T1 T2 := T1 -> T2.
Register arrow as elpi.derive.arrow.
Definition apply {T1 T2} (f : T1 -> T2) x := f x.
Register apply as elpi.derive.apply.

(* standalone *)
Elpi Command derive.eqType.ast.
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
