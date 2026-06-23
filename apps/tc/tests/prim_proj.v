From elpi Require Import tc.

Set Primitive Projections.
Record S := { sort :> Type }.
Unset Primitive Projections.

Class C (s : Type) := {}.

Instance SC (s : S) : C s := Build_C s.
