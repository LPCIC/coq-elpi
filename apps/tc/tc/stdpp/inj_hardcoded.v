From elpi Require Import elpi.
From stdpp Require Export base.
From elpi.apps Require Export tc.stdpp.inj_fun_ex.
From elpi.apps Require Import tc.compiler.

(* Global Hint Mode Inj - - ! ! -: typeclass_instances.
Global Hint Mode Inj - - ! ! !: typeclass_instances. *)

(* Elpi Debug "debug". *)
Elpi Accumulate TC_check Db tc.db.

(* Elpi add_instances Inj ignoreClasses Inj2 Equiv. *)
(* Elpi add_instances Inj ignoreInstances isInjf_eq. *)
Elpi add_instances Inj.
(* Elpi add_instances Inj ignoreInstances compose_inj. *)
(* Elpi add_instances instances compose_inj isInjf_eq isInjg_eq. *)
(* Elpi add_instances instances inr_inj. *)

Elpi Override TC TC_check.
