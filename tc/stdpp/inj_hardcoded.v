From elpi Require Import elpi.
From stdpp Require Export base.
From elpi.tc.stdpp Require Export inj_fun_ex.
From elpi.tc Require Import compiler.

(* Set Warnings "+elpi". *)

(* Unset Typeclass Resolution For Conversion. *)

(* The third param of inj cannot be flexible *)

Elpi Tactic HS_Inj.
Elpi Accumulate Db tc.db.

Elpi Accumulate lp:{{
  msolve L N :-
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.

  solve (goal _ _ Ty Sol _ as G) GL :- var Sol,
    (if (tc Ty X)  (refine X G GL ; coq.say "illtyped solution:" {coq.term->string X}) (GL = [seal G])).
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  tc {{Inj _ _ lp:T}} _ :- var T, !, coq.say "Inj: the instance function cannot be flexible", fail.
}}.
Elpi Typecheck.

(* Composition of injective functions  *)
Elpi Accumulate lp:{{
  tc {{@Inj lp:A lp:C lp:R1 lp:R3 (@compose lp:A lp:B lp:C lp:G lp:F) }} Sol :-
    tc {{@Inj lp:A lp:B lp:R1 lp:R2 lp:F}} InjF,
    tc {{@Inj lp:B lp:C lp:R2 lp:R3 lp:G}} InjG,
    Sol = {{@compose_inj lp:A lp:B lp:C lp:R1 lp:R2 lp:R3 lp:F lp:G lp:InjF lp:InjG }}. 
}}. 
Elpi Typecheck.

(* Prod map is inj *)
Elpi Accumulate lp:{{
   tc {{Inj eq eq (prod_map lp:F lp:G) }} Sol :-
    tc {{Inj eq eq lp:F}} InjF,
    tc {{Inj eq eq lp:G}} InjG,
    Sol = {{prod_map_inj lp:F lp:G lp:InjF lp:InjG }}.
}}.
Elpi Typecheck.

(* inr and inl are injective  *)
Elpi Accumulate lp:{{
  tc {{Inj eq eq inr}} {{inr_inj}}.
  tc {{Inj eq eq inl}} {{inl_inj}}.
}}.
Elpi Typecheck.

Elpi Accumulate lp:{{
  tc {{Inj eq eq (sum_map lp:F lp:G)}} Sol :- 
    coq.say "test",
    Sol = {{sum_map_inj lp:F lp:G lp:InjF lp:InjG}},
    tc {{Inj eq eq lp:F}} InjF, 
    tc {{Inj eq eq lp:G}} InjG.
}}.
Elpi Typecheck.

Elpi add_inst_by_path "Inj" "inj_fun_ex".