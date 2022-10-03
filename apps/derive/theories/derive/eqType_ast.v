From elpi Require Import elpi.

From elpi.apps.derive Extra Dependency "eqType.elpi" as eqType.

Elpi Db derive.eqType.db lp:{{

kind arguments type.
kind trm type.
kind eqType type.
kind constructor type.

type app    gref -> trm -> list trm -> trm.
type global gref -> trm.

type regular    trm -> arguments -> arguments.
type irrelevant trm -> arguments -> arguments.
type dependent  trm -> (trm -> arguments) -> arguments.
type stop       trm -> arguments.

type type-param         (trm -> eqType) -> eqType.
type value-param trm -> (trm -> eqType) -> eqType.
type inductive   inductive -> (trm -> list constructor) -> eqType.

type constructor constructor -> arguments -> constructor.

pred eqType i:inductive, o:eqType.

}}.

Definition arrow T1 T2 := T1 -> T2.
Register arrow as elpi.derive.arrow.
Definition apply {T1 T2} (f : T1 -> T2) x := f x.
Register apply as elpi.derive.apply.

Elpi Command derive.eqType.ast.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{

main [str S] :-
  std.assert! (coq.locate S (indt I)) "derive.eqType.ast: not an inductive",
  derive.eqType.ast.main I _.

}}.
Elpi Typecheck.
