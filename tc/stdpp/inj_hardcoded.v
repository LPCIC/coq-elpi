From elpi Require Import elpi.
From stdpp Require Export base.
Require Import Lia.
From elpi.tc.stdpp Require Export inj_fun_ex.

Set Typeclasses Debug.
Set Warnings "+elpi".

Elpi Db tc.db lp:{{
  pred tc o:term, o:term.
  tc {{ Inj _ _ lp:T }} _ :- var T, !, coq.say "fail on flexible function", fail.
}}.

Elpi Tactic HS_Inj.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  msolve L N :-
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.

  solve (goal _ _ Ty Sol _ as G) GL :- var Sol,
    (if (tc Ty X)  (refine X G GL ; coq.say "illtyped solution:" {coq.term->string X}) (GL = [seal G])).
}}.
Elpi Typecheck.

(* Get all instance from the inj_fun_ex file *)
Elpi Query lp:{{
  FILE-PATH = "inj_fun_ex",
  coq.TC.db-for {coq.locate "Inj"} F,
  std.map F (x\ r\ sigma TMP\ tc-instance TMP _ = x, r = global TMP) GR,
  std.map GR (x\ r\ sigma TMP\ global TMP = x, coq.gref->path TMP r) PATH,
  std.map2-filter GR PATH (a\b\r\ if (std.mem b FILE-PATH) (r = a) (fail)) RES,
  std.forall RES (x\ sigma Ty\ 
    coq.typecheck x Ty ok, 
    coq.elpi.accumulate _ "tc.db" (clause _ _ (tc Ty x))
  ).
}}.

Unset Typeclass Resolution For Conversion.

(* Composition of injective functions  *)
Elpi Accumulate tc.db lp:{{
  tc {{@Inj lp:A lp:C lp:R1 lp:R3 (@compose lp:A lp:B lp:C lp:G lp:F) }} Sol :-
    tc {{@Inj lp:A lp:B lp:R1 lp:R2 lp:F}} InjF,
    tc {{@Inj lp:B lp:C lp:R2 lp:R3 lp:G}} InjG,
    Sol = {{@compose_inj lp:A lp:B lp:C lp:R1 lp:R2 lp:R3 lp:F lp:G lp:InjF lp:InjG }}. 
}}. 
Elpi Typecheck.

(* Prod map is inj *)
Elpi Accumulate tc.db lp:{{
   tc {{Inj eq eq (prod_map lp:F lp:G) }} Sol :-
    tc {{Inj eq eq lp:F}} InjF,
    tc {{Inj eq eq lp:G}} InjG,
    Sol = {{prod_map_inj lp:F lp:G lp:InjF lp:InjG }}.
}}.
Elpi Typecheck.

(* inr and inl are injective  *)
Elpi Accumulate tc.db lp:{{
  tc {{Inj eq eq inr}} {{inr_inj}}.
  tc {{Inj eq eq inl}} {{inl_inj}}.
}}.

Elpi Accumulate tc.db lp:{{
  tc {{Inj eq eq (sum_map lp:F lp:G)}} Sol :- 
    Sol = {{sum_map_inj lp:F lp:G lp:InjF lp:InjG}},
    tc {{Inj eq eq lp:F}} InjF, 
    tc {{Inj eq eq lp:G}} INjG.
}}.