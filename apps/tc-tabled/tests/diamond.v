(* https://github.com/leanprover/lean4/blob/master/tests/lean/run/typeclass_diamond.lean *)

(* Diamond *)
Class T (α : Type) (n : nat).
Class R (α : Type) (n : nat).
Class L (α : Type) (n : nat).
Class B (α : Type) (n : nat).
Instance BtL α n `{B α n} : L α n := {}.
Instance BtR α n `{B α n} : R α n := {}.
Instance LtR α n `{L α n} : T α n := {}.
Instance RtR α n `{R α n} : T α n := {}.
Instance TtR α n `{T α n} : B α (S n) := {}.

Instance B0 α : B α 0 := {}.

(* (* Finished transaction in 0. secs (0.u,0.s) (successful) *) *)
(* Module Test0. Time Instance B_0 : B unit 0 := _. End Test0. *)

(* (* Finished transaction in 1.389 secs (1.387u,0.s) (successful) *) *)
(* Module Test225. Time Instance TtR225 : B unit 225 := _. End Test225. *)

(* (* Finished transaction in 12.928 secs (12.913u,0.011s) (successful) *) *)
(* Module Test450. Time Instance TtR450 : B unit 450 := _. End Test450. *)

(* (* Finished transaction in 38.213 secs (38.175u,0.001s) (successful) *) *)
(* Module Test675. Time Instance TtR675 : B unit 675 := _. End Test675. *)

(* (* Finished transaction in 104.095 secs (103.999u,0.074s) (successful) *) *)
(* Module Test900. Time Instance TtR900 : B unit 900 := _. End Test900. *)

(* (* Finished transaction in 175.868 secs (175.7u,0.026s) (successful) *) *)
(* Module Test1125. Time Instance TtR1125 : B unit 1125 := _. End Test1125. *)

(* (* Finished transaction in 355.404 secs (355.286u,0.021s) (successful) *) *)
(* Module Test1350. Time Instance B1350 : B unit 1350 := _. End Test1350. *)

(* (* Finished transaction in 534.246 secs (533.92u,0.079s) (successful) *) *)
(* Module Test1575. Time Instance TtR1575 : B unit 1575 := _. End Test1575. *)

(* (* Finished transaction in 849.83 secs (849.087u,0.431s) (successful) *) *)
(* Module Test1800. Time Instance B1800 : B unit 1800 := _. End Test1800. *)

(* (* Finished transaction in 1098.921 secs (1098.166u,0.083s) (successful) *) *)
(* Module Test2025. Time Instance TtR2025 : B unit 2025 := _. End Test2025. *)

(* (* Finished transaction in 1441.027 secs (1439.305u,0.752s) (successful) *) *)
(* Module Test2250. Time Instance B2250 : B unit 2250 := _. End Test2250. *)

From elpi Require Import elpi.
From elpi.apps Require Import tc.

(* Elpi TC Solver Activate TC.Solver. *)
Elpi TC Solver Override TC.Solver All.

TC.AddAllClasses.
TC.AddAllInstances.

(* (* Finished transaction in 3.082 secs (3.052u,0.026s) (successful) *) *)
(* (* Finished transaction in 5.362 secs (3.159u,0.319s) (successful) *) *)
(* (* Finished transaction in 7.973 secs (3.183u,0.686s) (successful) *) *)
(* Module Test700TC. Time Instance B700 : B unit 700 := _. End Test700TC. *)

(* (* Finished transaction in 13.83 secs (13.794u,0.003s) (successful) *) *)
(* (* Finished transaction in 12.364 secs (12.353u,0.s) (successful) *) *)
(* (* Finished transaction in 12.292 secs (12.195u,0.019s) (successful) *) *)
(* Module Test1400TC. Time Instance B1400 : B unit 1400 := _. End Test1400TC. *)

(* (* Finished transaction in 29.792 secs (28.346u,0.261s) (successful) *) *)
(* (* Finished transaction in 29.792 secs (28.346u,0.261s) (successful) *) *)
(* Module Test2100TC. Time Instance B2100 : B unit 2100 := _. End Test2100TC. *)

(* (* Finished transaction in 56.321 secs (54.822u,1.44s) (successful) *) *)
(* Module Test2800TC. Time Instance B2800 : B unit 2800 := _. End Test2800TC. *)

(* (* Finished transaction in 84.556 secs (82.008u,2.295s) (successful) *) *)
(* Module Test3500TC. Time Instance B3500 : B unit 3500 := _. End Test3500TC. *)

(* (* Finished transaction in 132.134 secs (125.754u,3.332s) (successful) *) *)
(* Module Test4200TC. Time Instance B4200 : B unit 4200 := _. End Test4200TC. *)

(* Finished transaction in 198.935 secs (162.925u,7.034s) (successful) *)
(* Module Test4900TC. Time Instance B4900 : B unit 4900 := _. End Test4900TC. *)

(* (* Stack overflow *) *)
(* (* Module Test5600TC. Time Instance B5600 : B unit 5600 := _. End Test5600TC. *) *)

Elpi TC Solver Override TC.Solver None.

From elpi.apps.tc_tabled Require Import tabled_type_class.

(* Diamond example in Rocq *)
Elpi TC Solver Activate TC.TabledSolver.
Elpi TC Solver Override TC.TabledSolver All.

(* Finished transaction in 1.911 secs (1.901u,0.007s) (successful) *)
Module Test50Tabled. Time Instance B50 : B unit 50 := _. End Test50Tabled. (* Takes: 20000 - 19650 steps *)

(* (* Finished transaction in 1.911 secs (1.901u,0.007s) (successful) *) *)
(* Module Test50Tabled. Time Instance B50 : B unit 50 := _. End Test50Tabled. (* Takes: 20000 - 19650 steps *) *)

(* (* Finished transaction in 12.3 secs (12.253u,0.032s) (successful) *) *)
(* Module Test100Tabled. Time Instance B100 : B unit 100 := _. End Test100Tabled. (* Takes: 20000 - 19300 steps *) *)

(* (* Finished transaction in 50.408 secs (50.147u,0.152s) (successful) *) *)
(* Module Test150Tabled. Time Instance B150 : B unit 150 := _. End Test150Tabled. (* Takes: 20000 - 18950 steps *) *)

(* (* Finished transaction in 154.541 secs (153.917u,0.547s) (successful) *) *)
(* Module Test200Tabled. Time Instance B200 : B unit 200 := _. End Test200Tabled. (* Takes: 20000 - 18600 steps *) *)

(* (* Finished transaction in 435.689 secs (434.456u,0.983s) (successful) *) *)
(* Module Test250Tabled. Time Instance B250 : B unit 250 := _. End Test250Tabled. (* Takes: 20000 - 18250 steps *) *)

(* (* Finished transaction in 694.726 secs (693.17u,1.298s) (successful) *) *)
(* Module Test300Tabled. Time Instance B300 : B unit 300 := _. End Test300Tabled. (* Takes: 20000 - 17900 steps *) *)

(* (* Finished transaction in 1473.093 secs (1437.954u,6.426s) (successful) *) *)
(* Module Test350Tabled. Time Instance B350 : B unit 350 := _. End Test350Tabled. (* Takes: 20000 - 17550 steps *) *)

(* (* Finished transaction in 2457.3 secs (2447.5u,3.536s) (successful) *) *)
(* Module Test400Tabled. Time Instance B400 : B unit 400 := _. End Test400Tabled. (* Takes: 20000 - 17200 steps *) *)

(* (* Finished transaction in 3465.9 secs (3306.596u,16.99s) (successful) *) *)
(* Module Test450Tabled. Time Instance B450 : B unit 450 := _. End Test450Tabled. (* Takes: 20000 - 16850 steps *) *)

(* (* Finished transaction in 4962.323 secs (4843.782u,17.345s) (successful) *) *)
(* Module Test500Tabled. Time Instance B500 : B unit 500 := _. End Test500Tabled. (* Takes: 20000 - 16500 steps *) *)
