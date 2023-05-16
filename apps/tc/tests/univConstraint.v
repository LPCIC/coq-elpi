From Coq Require Export List.
From elpi.apps Require Export compiler.
Global Generalizable All Variables.

Elpi Override TC TC_check All.

Class ElemOf A B := elem_of: A -> B -> Prop.
Class Elements A C := elements: C -> list A.

Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here (x : A) l : elem_of x (x :: l)
  | elem_of_list_further (x y : A) l : elem_of x l -> elem_of x (y :: l).
Global Existing Instance elem_of_list.

Elpi AddInstances ElemOf.

Inductive NoDup {A} : list A -> Prop :=
  | NoDup_nil_2 : NoDup nil
  | NoDup_cons_2 x l : not (elem_of x l) -> NoDup l -> NoDup (x :: l).

Class FinSet A C `{ElemOf A C,Elements A C} : Prop := {
  NoDup_elements (X : C) : @NoDup A (elements X)
}.

Fail Class FinSet1 A C `{ElemOf A C,Elements A C} : Prop := {
  NoDup_elements (X : C) : NoDup (elements X)
}.