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

(* Finished transaction in 0.004 secs (0.004u,0.s) (successful) *)
Module Test20. Time Instance TtR20 : B unit 20 := _. End Test20.

(* Finished transaction in 1.372 secs (1.195u,0.03s) (successful) *)
Module Test200. Time Instance TtR200 : B unit 200 := _. End Test200.

(* Finished transaction in 4.842 secs (4.084u,0.147s) (successful) *)
Module Test300. Time Instance TtR300 : B unit 300 := _. End Test300.

(* Finished transaction in 23.508 secs (22.228u,0.258s) (successful) *)
Module Test500. Time Instance TtR500 : B unit 500 := _. End Test500.

(* Finished transaction in 31.622 secs (28.185u,0.517s) (successful) *)
Module Test550. Time Instance TtR550 : B unit 550 := _. End Test550.

(* Finished transaction in 31.622 secs (28.185u,0.517s) (successful) *)
Module Test1000. Time Instance TtR1000 : B unit 1000 := _. End Test1000.
