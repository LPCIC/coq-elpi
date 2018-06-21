# Derive

This directory contains the elpi files implementing various automatic
derivation of terms.  The corresponding .v files, defining the Coq commands,
are in `theories/derive/`.


![Big picture](derive.svg)

## derive.isK

Given an inductive `I` type it generates for each constructor `K` a function to `bool` names `${prefix}K` where `prefix` is `is` by default. The type of `isK` is `forall params idxs, I params idxs -> bool`. Example:
```coq
Elpi derive.isK list. Print isnil. (*
isnil = 
  fun (A : Type) (i : list A) =>
    match i with
    | nil => true
    | (_ :: _)%list => false
    end
*)
```

status: ok

coverage: ?? full CIC

todo: db on term, not GR

## derive.projK

Given an inductive `I` type it generates for each constructor `K` and argument `i` of this constructor a function named `${prefix}Ki` where `prefix` is `proj` by default. The type of `projKi` is `forall params idxs default_value_for_args, I params idxs -> arg_i`. Example:
```coq
Elpi derive.projK Vector.t. Print projcons1. (*
projcons1 = 
  fun (A : Type) (H : nat) (h : A) (n : nat) (_ : Vector.t A n) (i : Vector.t A H) =>
    match i with
    | Vector.nil _ => h
    | Vector.cons _ h0 _ _ => h0
    end
 : forall (A : Type) (H : nat),
          A -> forall n : nat, Vector.t A n ->
          Vector.t A H -> A
```
The intended use is to perform injection, i.e. one aleady has a term of the shape `K args` and
can just use these args to provide the default values.

If the project argument's type depends on the value of other arguments, then it is boxed using `existT`.
```coq
Check projcons3. (*
projcons3
     : forall (A : Type) (H : nat),
       A -> forall n : nat, Vector.t A n ->
       Vector.t A H -> {i1 : nat & Vector.t A i1}
*)
```

status: ok

coverage: ?? full CIC

todo: db on term not GR

## ltac.injection

`injection H EqAB PL` given an equation `H` of type `EqAB` returns a list
of equations `PL`. `EqAB` is expected to be of the form `K .. = K ..` for
a constructor `K`.

coverage: does not do the smart thing when the obtained equations are like `{ i : nat & Vector.t A i } = ...` in which case, given that `nat` is `eqType` one could obtain systematically the two equalities.

status: experimental API

todo: remove the last occurrence of `hole` so that no elaboration is needed

## ltac.discriminate

`discriminate H EqAB G PG` given an equation `H` of type `EqAB` and
a goal `G` it provides a proof `PG`. It asserts that `EqAB` is of
the form `K1 .. = K2 ..` when `K1` is a constructor different from `K2`.

coverage: full CIC

status: ok

todo: `eq_f` and `boold_discr` should be moved to another .v file


## derive.bcongr

We call a boolean congruence lemma an instance of the `reflect` predicate
on a proposition `K x1..xn = K y1..yn` and a boolean expression `b1 && .. bn`.
Eg
```coq
Elpi derive.bcongr list.
Check nil_congr : forall A, reflect (@nil A = nil) true.
Check cons_congr :
  forall A,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (xs ys : list A) b2, reflect (xs = ys) b2 ->
    reflect (cons x xs = cons y ys) (b1 && b2).
```

status: ok

coverage: polynomial types.

todo: internal documentation. example of non-polynomial type.

## derive.eq

Generates a boolean comparison function.

```coq
Elpi derive.eq list. Check list_eq. (*
list_eq
     : forall A : Type,
       (A -> A -> bool) -> list A -> list A -> bool
*)
```

coverage: works with indexes by generalizing to equality on types that differ in the indexes. Does not cover quantifications on type, even if the come with a comparison function attached. Bug no tree data type.

status: ok

todo: document the db interface




