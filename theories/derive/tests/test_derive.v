From elpi Require Import derive.

Elpi derive nat.
Print Module nat.

Check nat.eq : nat -> nat -> bool.
Check nat.isO : nat -> bool.
Check nat.isS : nat -> bool.
Check nat.map : nat -> nat.
Check nat.proj1S : nat -> nat -> nat.
Fail Check nat.map : nat -> nat.

Elpi derive list.
Print Module list.

Check list.eq  : forall A, (A -> A -> bool) -> list A -> list A -> bool.
Check list.isnil  : forall A, list A -> bool.
Check list.iscons : forall A, list A -> bool.
Check list.map : forall A B, (A -> B) -> list A -> list B.
Check list.proj1cons : forall A, A -> list A -> A.
Check list.proj2cons : forall A, A -> list A -> list A -> list A.