From elpi Require Import tc.

Set Primitive Projections.
Record S := { sort :> Type }.
Unset Primitive Projections.

Elpi cs default (S).

Class C (s : Type) := {}.

Instance SC (s : S) : C s := Build_C s.
