# Canonical solution

The `canonical_solution` app enables to program Coq canonical structure solutions in Elpi.

This app is experimental.

## The cs predicate

The `cs` predicate lives in the database `cs.db`

```elpi
% predicate [cs Ctx Proj Rhs Sol] used to find Sol such that Proj Sol = Rhs, where
% - [Ctx] is the context
% - [Proj] is the projector of some structure, applied to the structure's parameters if any
% - [Rhs] the term to find a structure on.
pred cs goal-ctx, term, term-> term.
```

By addings rules for this predicate one can recover from a CS instance search failure
error, that is when `Lhs` and `Rhs` are not unifiable using a canonical structure registered
by Coq.

## Simple example of canonical solution

This example declares a structure `S` with a projection `sort` and declares
a canonical solution for `nat` in `S`.

```coq
From elpi.apps Require Import cs.
From Coq Require Import Bool.

Structure S : Type := mkS { sort :> Type }.

Elpi Accumulate cs.db lp:{{

cs _ {{ sort }} {{ nat }} {{ mkS nat }}.

}}.

Check eq_refl _ : (sort _) = nat.
```
