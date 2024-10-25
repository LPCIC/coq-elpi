From elpi.apps Require Import cs.
From Coq Require Import Bool.

Structure S (T : Type) : Type :=
  { sort :> T -> T }.

Elpi Accumulate canonical_solution lp:{{

cs _ {{ sort lp:T }} {{ @id lp:T }} {{ Build_S lp:T (@id lp:T) }}.

}}.

Check 1.
Check eq_refl _ : (sort nat _) = @id nat.
Check 11.
Check eq_refl _ : (sort nat _) 1 = @id nat 1.
Definition id1 := id.
Check 2.
Check eq_refl _ : (sort nat _) = @id1 nat.
Definition sort1 := sort.
Check 3.
Check eq_refl _ : (sort1 nat _) = @id nat.
Check 4.
Check eq_refl _ : (sort1 nat _) = @id1 nat.


