From elpi.apps Require Import cs.
From Coq Require Import Bool.

Elpi Override CS All.

Structure S : Type :=
  { sort :> Type }.

Elpi Accumulate cs.db lp:{{

canonical-solution _ {{ sort lp:Sol }} {{ nat }} :-
  Sol = {{ Build_S nat }}.

}}.
Elpi Typecheck canonical_solution.

Check 1.
Check eq_refl _ : (sort _) = nat.
Definition nat1 := nat.
Check 2.
Check eq_refl _ : (sort _) = nat1.
Definition sort1 := sort.
Check 3.
Check eq_refl _ : (sort1 _) = nat.
Check 4.
Check eq_refl _ : (sort1 _) = nat1.


Elpi Accumulate cs.db lp:{{

canonical-solution _ {{ sort lp:Sol }} {{ bool }} :-
  % typing is wired in, do we want this?
  std.spy(Sol = {{ Prop }}).

}}.
Elpi Typecheck canonical_solution.


Check eq_refl _ : (sort _) = bool.
