From elpi Require Import elpi.
From stdpp Require Export base.
From elpi.tc.stdpp Require Export inj_fun_ex.
From elpi.tc Require Import compiler.

Set Warnings "+elpi".

(* Unset Typeclass Resolution For Conversion. *)

(* The third param of inj cannot be flexible *)

Elpi Accumulate tc.db lp:{{
  tc {{Inj _ _ lp:T}} _ :- var T, !, coq.say "Inj: the instance function cannot be flexible", fail.
}}.
Elpi Typecheck TC_check.

(* Composition of injective functions  *)
Elpi Accumulate tc.db lp:{{
  tc {{@Inj lp:A lp:C lp:R1 lp:R3 (@compose lp:A lp:B lp:C lp:G lp:F) }} Sol :-
    tc {{@Inj lp:A lp:B lp:R1 lp:R2 lp:F}} InjF,
    tc {{@Inj lp:B lp:C lp:R2 lp:R3 lp:G}} InjG,
    Sol = {{@compose_inj lp:A lp:B lp:C lp:R1 lp:R2 lp:R3 lp:F lp:G lp:InjF lp:InjG }}. 
}}. 
Elpi Typecheck TC_check.

(* Prod map is inj *)
Elpi Accumulate tc.db lp:{{
   tc {{Inj eq eq (prod_map lp:F lp:G) }} Sol :-
    tc {{Inj eq eq lp:F}} InjF,
    tc {{Inj eq eq lp:G}} InjG,
    Sol = {{prod_map_inj lp:F lp:G lp:InjF lp:InjG }}.
}}.
Elpi Typecheck TC_check.

Elpi Accumulate tc.db lp:{{
  tc {{Inj eq eq (sum_map lp:F lp:G)}} Sol :- 
    coq.say "test",
    Sol = {{sum_map_inj lp:F lp:G lp:InjF lp:InjG}},
    tc {{Inj eq eq lp:F}} InjF, 
    tc {{Inj eq eq lp:G}} InjG.
}}.
Elpi Typecheck TC_check.

Elpi add_inst_by_path "Inj".

Elpi Override TC TC_check.