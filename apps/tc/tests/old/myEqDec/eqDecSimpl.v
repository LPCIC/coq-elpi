Require Export Bool Arith List.
From Coq Require Import FunctionalExtensionality.

Export ListNotations.
Generalizable Variables A B.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Definition neqb {A} `{Eqb A} (x y : A) := negb (x == y). 

Local Instance eqU : Eqb unit := { eqb x y := true }.
Local Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

From elpi Require Import elpi.
From elpi.apps Require Export tc.compiler.

Elpi Accumulate TC_check lp:{{
  tc {{ Eqb unit }} {{ eqU }}.
  tc {{ Eqb bool }} {{ eqB }}.
  tc {{ Eqb (prod lp:A lp:B) }} {{ @eqP _ _ lp:EqA lp:EqB }} :- 
    tc {{ Eqb lp:A }} EqA,
    tc {{ Eqb lp:B }} EqB.
}}.
Elpi Print TC_check.

Check ((tt, (tt, true)) == (tt, (tt, true))).
Check (1 == 2).
Compute (fst (1, 2)).

Local Instance eq_nat : Eqb nat := {
  eqb := fix aux i1 i2 := 
  match i1, i2 return bool with
    | O, O => true 
    | S x, S y => aux x y
    | _, _ => false 
  end 
}.
Local Instance eq_list `(eqa : (Eqb A)) : Eqb (list A) :=
  { eqb := fix aux (x y : list A) :=
    match x, y return bool with
    | [], [] => true 
    | x :: xs, y :: ys => (eqb x y) && (aux xs ys)
    | _, _ => false
    end }.
Local Instance eq_bool_to_bool `(Eqb A) : Eqb (bool -> A) :=
{
  eqb f g := (f true == g true) && (f false == g false)
}.

(* Elpi AddInstances Eqb. *)


Elpi Override TC TC_check Only Eqb.
Elpi AddInstances Eqb.

(* Set Typeclasses Debug. *)
Check (fun n m : _ => eqb n m).
