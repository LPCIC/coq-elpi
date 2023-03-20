Require Import String Arith Bool List.
Open Scope string_scope.
Import ListNotations.

Class Show A : Type :=
  {
    show : A -> string
  }.

#[export] Instance showBool : Show bool :={
    show := fun b:bool => if b then "true" else "false"
}.

Set Typeclasses Debug.
Check (show false).

Inductive primary := Red | Green | Blue.
#[export] Instance showPrimary : Show primary :=
  {
    show :=
      fun c:primary =>
        match c with
        | Red => "Red"
        | Green => "Green"
        | Blue => "Blue"
        end
  }.

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.
Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".
#[export] Instance showNat : Show nat := { show := string_of_nat }.

#[export] Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {
    show p :=
      let (a,b) := p in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.

Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => append (append (s h) ", ") (showListAux s t)
  end.
#[export] Instance showList {A : Type} `{Show A} : Show (list A) :=
  {
    show l := append "[" (append (showListAux show l) "]")
  }.


Compute (show (true,42)).


Definition eg42 := show 42.
Set Printing Implicit.
Print eg42.
Unset Printing Implicit.

Check (show (true,[[3]])).
Check (show (_,42)).
