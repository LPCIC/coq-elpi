Require Import List Bool String.
Import ListNotations.
Open Scope string_scope.
(* Elpi *)
From elpi Require Import elpi.
From elpi.tc.myEqDec Require Import eqDec_hardcoded.

(* Override the default behavior *)
Elpi Override TC HS_EqDec.

Print Instances EqDec.
(* 
eq_nat : EqDec nat
eq_bin : forall {A : Type}, EqDec A -> EqDec bin
eq_bool_to_bool : forall {A : Type}, EqDec A -> EqDec (bool -> A)
eq_letter : forall {A : Type}, EqDec A -> EqDec letter
eq_unit : EqDec unit
eq_prod :
forall {A : Type}, EqDec A -> forall B : Type, EqDec B -> EqDec (A * B)
eq_list : forall {A : Type}, EqDec A -> EqDec (list A)
eq_bool : EqDec bool
eq_bin2 :
forall {A : Type}, EqDec A -> forall B : Type, EqDec B -> EqDec bin2
*)
(* Print HintDb typeclass_instances. *)

Set Typeclasses Debug.

Check (LA 3 == LA 3).
Compute (XA == XA).
Check ("aa" == "aa").

(* OK due to `tc {{ EqDec lp:A }} _ :- var A, !.` *)
Check (fun b => [1] == b).
Check ([1] == []).
Compute (nil == nil).
Compute (fun b => b == []).
Compute (fun b => [] == b).
Compute ((L, L) == (N 5 L L, L)).
Compute (N1 5 (N 4 L L) L == N1 5 (N 3 L L) L).

(* OK *)
Check (fun a b : list nat => a == b).
Check (fun a b : _ => a == b).
Check (fun b => [1] == b).
Compute ([1] == [1]).
Compute (nil == @nil nat).
Compute ([true] == [false]).
Compute (tt == tt).
Compute (N1 5 L (N false L L) == N1 5 L (N false L L)).
Compute (N1 5 (N 4 L L) L == N1 5 (N 3 L L) (@L nat)).
Compute (N 5 L L == L).
Check (fun n m : nat  => n == m).
Check (fun b q : bool => b == q).
Check (fun n m:(nat * nat) => n == m).
Check (fun a b : (list bool * list nat) => a == b).
Check (false == true).
Compute (8 == 9).
Compute (8 == 8).
