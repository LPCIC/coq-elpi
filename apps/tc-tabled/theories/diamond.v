(* Diamond example in Rocq *)
Class T (alpha : Type) (n : nat).
Class R (alpha : Type) (n : nat).
Class L (alpha : Type) (n : nat).
Class B (alpha : Type) (n : nat).
Instance BtL alpha n `{B alpha n} : L alpha n := {}.
Instance BtR alpha n `{B alpha n} : R alpha n := {}.
Instance LtR alpha n `{L alpha n} : T alpha n := {}.
Instance RtR alpha n `{R alpha n} : T alpha n := {}.
Instance TtR alpha n `{T alpha n} : B alpha (S n) := {}.

Instance B0 alpha : B alpha 0 := {}.

(* Rocq: Finished transaction in 0.151 secs (0.151u,0.s) (successful) *)
Module Test100. Time Instance TtR100 : B unit 100 := _. End Test100.

(* Rocq: Finished transaction in 1.372 secs (1.195u,0.03s) (successful) *)
Module Test200. Time Instance TtR200 : B unit 200 := _. End Test200.

(* Rocq: Finished transaction in 4.842 secs (4.084u,0.147s) (successful) *)
Module Test300. Time Instance TtR300 : B unit 300 := _. End Test300.

(* Rocq: Finished transaction in 12.245 secs (11.568u,0.091s) (successful) *)
Module Test400. Time Instance TtR400 : B unit 400 := _. End Test400.

(* Rocq: Finished transaction in 23.508 secs (22.228u,0.258s) (successful) *)
Module Test500. Time Instance TtR500 : B unit 500 := _. End Test500.

(* Rocq: Finished transaction in 37.784 secs (37.582u,0.059s) (successful) *)
Module Test600. Time Instance TtR600 : B unit 600 := _. End Test600.

(* Rocq: Finished transaction in 66.476 secs (66.261u,0.106s) (successful) *)
Module Test700. Time Instance TtR700 : B unit 700 := _. End Test700.

(* Rocq: Finished transaction in 77.99 secs (77.174u,0.11s) (successful) *)
Module Test800. Time Instance TtR800 : B unit 800 := _. End Test800.

(* Rocq: Finished transaction in 106.952 secs (106.779u,0.025s) (successful) *)
Module Test900. Time Instance TtR900 : B unit 900 := _. End Test900.

(* Rocq: Finished transaction in 184.144 secs (183.71u,0.117s) (successful) *)
Module Test1000. Time Instance TtR1000 : B unit 1000 := _. End Test1000.

(* Ratio: ~ time: 2^(x/100) secs *)

(* Rocq: Finished transaction in 1476.371 secs (1463.871u,3.989s) (successful) *)
Module Test2000. Time Instance TtR2000 : B unit 2000 := _. End Test2000.
