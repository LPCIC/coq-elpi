# Canonical solution

The `canonical_solution` app enables to program Coq canonical structure solutions in Elpi.

This app is experimental.

## The cs predicate

The `cs` predicate lives in the database `cs.db`

```elpi
% predicate [cs Ctx Lhs Rhs] used to unify Lhs with Rhs, with
% - [Ctx] is the context
% - [Lhs] and [Rhs] are the terms to unify
:index (0 6 6)
pred cs i:goal-ctx, o:term, o:term.
```

By adding rules for this predicate one can recover from a CS instance search failure
error, that is when `Lhs` and `Rhs` are not unifiable using a canonical structure registered
by Coq.

## Simple example of canonical solution

This example declares a structure `S` with a projection `sort` and declares
a canonical solution for `nat` in `S`.

```coq
From elpi.apps Require Import cs.
From Coq Require Import Bool.

Structure S : Type :=
  { sort :> Type }.

Elpi Accumulate cs.db lp:{{

cs _ {{ sort lp:Sol }} {{ nat }} :-
  Sol = {{ Build_S nat }}.

}}.
Elpi Typecheck canonical_solution.

Check eq_refl _ : (sort _) = nat.
```
