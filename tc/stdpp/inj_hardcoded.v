From elpi Require Import elpi.
From stdpp Require Export base.
From elpi.tc.stdpp Require Export inj_fun_ex.
From elpi.tc Require Import compiler.

Set Warnings "+elpi".

(* Elpi add_instances Inj. *)

(* Global Hint Mode Inj - - ! ! !: typeclass_instances. *)

Elpi Accumulate TC_check Db tc.db.

(* Elpi Query TC_check lp:{{
  F = {{TCForall}},
  (app [global (X) | _]) = F,
  coq.hints.modes X "typeclass_instances" R,
  coq.CS.db L,
  coq.say "Ciao".
}}. *)

(* Elpi add_instances "Inj" exclude isInjf_eq. *)
Elpi add_instances "Inj".
(* Elpi add_instances "Inj" exclude "compose_inj". *)
(* Elpi add_instances "instances" "compose_inj" "isInjf_eq" "isInjg_eq". *)
(* Elpi add_instances "instances" "inr_inj". *)


Elpi Override TC TC_check.
(* Check (_ : @Inj _ _ _ _ _). *)

