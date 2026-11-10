(* https://github.com/leanprover/lean4/blob/master/tests/lean/run/typeclass_diamond.lean *)

(* Diamond *)
Class Top1   (n : nat) : Type.
Class Bot1   (n : nat) : Type.
Class Left1  (n : nat) : Type.
Class Right1 (n : nat) : Type.

Instance Bot1Inst : Bot1 0 := {}.
Instance Left1ToBot1   (n : nat) `{Left1 n}  : Bot1 n := {}.

Instance Right1ToBot1  (n : nat) `{Right1 n} : Bot1 n := {}.
Instance Top1ToLeft1   (n : nat) `{Top1 n}   : Left1 n := {}.
Instance Top1ToRight1  (n : nat) `{Top1 n}   : Right1 n := {}.
Instance Bot1ToTopSucc (n : nat) `{Bot1 n}   : Top1 (S n) := {}.

Class Top2 (n : nat) : Type.
Class Bot2   (n : nat) : Type.
Class Left2  (n : nat) : Type.
Class Right2 (n : nat) : Type.

Instance Left2ToBot2   (n : nat) `{Left2 n}  : Bot2 n := {}.
Instance Right2ToBot2  (n : nat) `{Right2 n} : Bot2 n := {}.
Instance Top2ToLeft2   (n : nat) `{Top2 n}   : Left2 n := {}.
Instance Top2ToRight2  (n : nat) `{Top2 n}   : Right2 n := {}.
Instance Bot2ToTopSucc (n : nat) `{Bot2 n}   : Top2 (S n) := {}.

Class Top (n : nat) : Type.

Instance Top1ToTop (n : nat) `{Top1 n} : Top n := {}.
Instance Top2ToTop (n : nat) `{Top2 n} : Top n := {}.

(* (* Finished transaction in 0.001 secs (0.001u,0.s) (successful) *) *)
(* Module Top4Rocq. Time Instance Top4 : Top 4 := _. End Top4Rocq. *)

(* (* Finished transaction in 0.021 secs (0.021u,0.s) (successful) *) *)
(* Module Top8Rocq. Time Instance Top8 : Top 8 := _. End Top8Rocq. *)

(* (* Finished transaction in 4.661 secs (4.661u,0.s) (successful) *) *)
(* Module Top16Rocq. Time Instance Top16 : Top 16 := _. End Top16Rocq. *)

(* (* Finished transaction in 0.719 secs (0.717u,0.s) (successful) *) *)
(* Module Top17Rocq. Time Instance Top17 : Top 17 := _. End Top17Rocq. *)

(* (* Finished transaction in 1.409 secs (1.407u,0.s) (successful) *) *)
(* Module Top18Rocq. Time Instance Top18 : Top 18 := _. End Top18Rocq. *)

(* (* Finished transaction in 2.789 secs (2.785u,0.002s) (successful) *) *)
(* Module Top19Rocq. Time Instance Top19 : Top 19 := _. End Top19Rocq. *)

(* (* Finished transaction in 5.602 secs (5.597u,0.001s) (successful) *) *)
(* Module Top20Rocq. Time Instance Top20 : Top 20 := _. End Top20Rocq. *)

(* (* Finished transaction in 170.346 secs (170.255u,0.004s) (successful) *) *)
(* Module Top21Rocq. Time Instance Top21 : Top 21 := _. End Top21Rocq. *)

(* (* Finished transaction in 351.702 secs (351.432u,0.033s) (successful) *) *)
(* Module Top22Rocq. Time Instance Top22 : Top 22 := _. End Top22Rocq. *)

(* (* Finished transaction in 699.508 secs (699.034u,0.059s) (successful) *) *)
(* Module Top23Rocq. Time Instance Top23 : Top 23 := _. End Top23Rocq. *)

From elpi Require Import elpi.
From elpi.apps Require Import tc.

Elpi TC Solver Activate TC.Solver.
Elpi TC Solver Override TC.Solver All.

TC.AddAllClasses.
TC.AddAllInstances.

(* ELPI TC solver *)

(* (* Finished transaction in 0.029 secs (0.029u,0.s) (successful) *) *)
(* Module Top4ELPI_TC. Time Instance Top4 : Top 4 := _. End Top4ELPI_TC. *)

(* (* Finished transaction in 0.035 secs (0.035u,0.s) (successful) *) *)
(* Module Top8ELPI_TC. Time Instance Top8 : Top 8 := _. End Top8ELPI_TC. *)

(* (* Finished transaction in 0.368 secs (0.367u,0.s) (successful) *) *)
(* Module Top16ELPI_TC. Time Instance Top16 : Top 16 := _. End Top16ELPI_TC. *)

(* (* Finished transaction in 0.719 secs (0.717u,0.s) (successful) *) *)
(* Module Top17ELPI_TC. Time Instance Top17 : Top 17 := _. End Top17ELPI_TC. *)

(* (* Finished transaction in 1.409 secs (1.407u,0.s) (successful) *) *)
(* Module Top18ELPI_TC. Time Instance Top18 : Top 18 := _. End Top18ELPI_TC. *)

(* (* Finished transaction in 2.789 secs (2.785u,0.002s) (successful) *) *)
(* Module Top19ELPI_TC. Time Instance Top19 : Top 19 := _. End Top19ELPI_TC. *)

(* (* Finished transaction in 5.602 secs (5.597u,0.001s) (successful) *) *)
(* Module Top20ELPI_TC. Time Instance Top20 : Top 20 := _. End Top20ELPI_TC. *)

(* (* Finished transaction in 12.295 secs (12.281u,0.002s) (successful) *) *)
(* Module Top21ELPI_TC. Time Instance Top21 : Top 21 := _. End Top21ELPI_TC. *)

(* (* Finished transaction in 27.964 secs (27.951u,0.003s) (successful) *) *)
(* Module Top22ELPI_TC. Time Instance Top22 : Top 22 := _. End Top22ELPI_TC. *)

(* (* Finished transaction in 49.262 secs (49.231u,0.008s) (successful) *) *)
(* Module Top23ELPI_TC. Time Instance Top23 : Top 23 := _. End Top23ELPI_TC. *)

(* (* Finished transaction in 101.836 secs (101.792u,0.017s) (successful) *) *)
(* Module Top24ELPI_TC. Time Instance Top24 : Top 24 := _. End Top24ELPI_TC. *)

(* (* Finished transaction in 205.469 secs (205.309u,0.032s) (successful) *) *)
(* Module Top25ELPI_TC. Time Instance Top25 : Top 25 := _. End Top25ELPI_TC. *)


(* / ELPI TC solver *)

Elpi TC Solver Override TC.Solver None.

From elpi.apps.tc_tabled Require Import tabled_type_class.

(* Diamond example in Rocq *)
Elpi TC Solver Activate TC.TabledSolver.
Elpi TC Solver Override TC.TabledSolver All.

(* Tabled solver *)

(* Finished transaction in 0.023 secs (0.023u,0.s) (successful) *)
Module Top4Tabled. Time Instance Top4 : Top 4 := _. End Top4Tabled.

(* Finished transaction in 0.054 secs (0.054u,0.s) (successful) *)
Module Top8Tabled. Time Instance Top8 : Top 8 := _. End Top8Tabled.

(* Finished transaction in 0.201 secs (0.197u,0.003s) (successful) *)
Module Top16Tabled. Time Instance Top16 : Top 16 := _. End Top16Tabled.

(* Finished transaction in 0.273 secs (0.267u,0.005s) (successful) *)
Module Top17Tabled. Time Instance Top17 : Top 17 := _. End Top17Tabled.

(* Finished transaction in 0.255 secs (0.253u,0.s) (successful) *)
Module Top18Tabled. Time Instance Top18 : Top 18 := _. End Top18Tabled.

(* Finished transaction in 0.289 secs (0.286u,0.001s) (successful) *)
Module Top19Tabled. Time Instance Top19 : Top 19 := _. End Top19Tabled.

(* Finished transaction in 0.369 secs (0.36u,0.007s) (successful) *)
Module Top20Tabled. Time Instance Top20 : Top 20 := _. End Top20Tabled.

(* Finished transaction in 0.363 secs (0.351u,0.011s) (successful) *)
Module Top21Tabled. Time Instance Top21 : Top 21 := _. End Top21Tabled.

(* Finished transaction in 0.372 secs (0.372u,0.s) (successful) *)
Module Top22Tabled. Time Instance Top22 : Top 22 := _. End Top22Tabled.

(* Finished transaction in 0.419 secs (0.415u,0.003s) (successful) *)
Module Top23Tabled. Time Instance Top23 : Top 23 := _. End Top23Tabled.

(* Finished transaction in 0.507 secs (0.506u,0.s) (successful) *)
Module Top24Tabled. Time Instance Top24 : Top 24 := _. End Top24Tabled.

(* Finished transaction in 0.525 secs (0.519u,0.005s) (successful) *)
Module Top25Tabled. Time Instance Top25 : Top 25 := _. End Top25Tabled.

(* Finished transaction in 3.148 secs (3.147u,0.s) (successful) *)
Module Top50Tabled. Time Instance Top50 : Top 50 := _. End Top50Tabled.

(* Finished transaction in 10.138 secs (10.041u,0.092s) (successful) *)
Module Top75Tabled. Time Instance Top75 : Top 75 := _. End Top75Tabled.

(* Finished transaction in 26.328 secs (26.289u,0.006s) (successful) *)
Module Top100Tabled. Time Instance Top100 : Top 100 := _. End Top100Tabled.

(* Finished transaction in 48.959 secs (48.772u,0.174s) (successful) *)
Module Top125Tabled. Time Instance Top125 : Top 125 := _. End Top125Tabled.

(* Finished transaction in 87.289 secs (87.152u,0.13s) (successful) *)
Module Top150Tabled. Time Instance Top150 : Top 150 := _. End Top150Tabled.

(* Finished transaction in 152.848 secs (152.537u,0.223s) (successful) *)
Module Top175Tabled. Time Instance Top175 : Top 175 := _. End Top175Tabled.

(* Finished transaction in 247.147 secs (246.117u,0.948s) (successful) *)
Module Top200Tabled. Time Instance Top200 : Top 200 := _. End Top200Tabled.

(* / Tabled solver *)
(* Finished transaction in 726.238 secs (725.633u,0.254s) (successful) *)
