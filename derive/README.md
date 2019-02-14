# Derive

This directory contains the elpi files implementing various automatic
derivation of terms.  The corresponding .v files, defining the Coq commands,
are in `theories/derive/`.

![Big picture](derive.svg)


## derive.isK

Given an inductive type it generates for each constructor a function that tests testing if a term is a specific
contructor.

Example: 
```coq
Elpi derive.isK list.
Print list_is_nil. (*
list_is_nil = 
  fun (A : Type) (i : list A) =>
    match i with
    | nil => true
    | _ => false
    end
*)
```

## derive.projK

Given an inductive type it generates for each constructor `K` and argument
`i` of this constructor a function extracting that argument (provided enough
default values).

```coq
Elpi derive.projK Vector.t.
Check projcons1. (*
projcons1 
 : forall (A : Type) (H : nat),
          A -> forall n : nat, Vector.t A n ->
          Vector.t A H -> A
```
The intended use is to perform injection, i.e. one aleady has a term of the
shape `K args` and can just use these args to provide the default values.

If the project argument's type depends on the value of other arguments, then it
is boxed using `existT`.
```coq
Check projcons3. (*
projcons3
     : forall (A : Type) (H : nat),
       A -> forall n : nat, Vector.t A n ->
       Vector.t A H -> {i1 : nat & Vector.t A i1}
*)
```

## ltac.injection

`injection H EqAB PL` given an equation `H` of type `EqAB` returns a list
of equations `PL`. `EqAB` is expected to be of the form `K .. = K ..` for
a constructor `K`.

coverage: does not do the smart thing when the obtained equations are like `{ i : nat & Vector.t A i } = ...` in which case, given that `nat` is `eqType` one could obtain systematically the two equalities.

status: experimental API

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

```coq
Elpi derive.bcongr list.
Check nil_congr : forall A, reflect (@nil A = @nil A) true.
Check cons_congr :
  forall A,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (xs ys : list A) b2, reflect (xs = ys) b2 ->
    reflect (cons x xs = cons y ys) (b1 && b2).
```

## derive.eq

Generates a boolean comparison function.

```coq
Elpi derive.eq list. 
Check list_eq. (*
list_eq
     : forall A : Type,
       (A -> A -> bool) -> list A -> list A -> bool
*)
```

## derive.eqK

Generates, for each constructor, the correctness lemma for the comparison
function.

```coq
Elpi derive.eqK list.

Check eq_axiom_nil : forall A fa, axiom (list A) (list_eq A fa) (@nil A).

Check eq_axiom_cons : forall A fa,
  forall x, axiom A fa x ->
  forall xs, axiom (list A) (list_eq A fa) xs ->
    axiom (list A) (list_eq A fa) (cons x xs).
```

## derive.map

Map a container over its parameters. 

```coq
Elpi derive.map list.
Check list_map : forall A B, (A -> B) -> list A -> list B.
```

## derive.param1

Unary parametricity translation.

```coq
Elpi derive.param1 nat.
Print is_nat. (*
Inductive is_nat : nat -> Type :=
| is_O : is_nat 0
| is_S : forall n : nat, is_nat n -> is_nat (S n) *)
```

## derive.param1P

Unary parametricity translation reflects typing.

```coq
Elpi derive.param1P is_nat.
Check nat_is_nat : forall x : nat, is_nat x.
```

## derive.induction

Induction principle for `T` based on `is_T`

```coq
Elpi derive.induction list.
Check list_induction :
  forall (A : Type) (PA : A -> Type) P,
    P (nil A) ->
    (forall x : A, PA x -> forall xs, P xs -> P (cons A x xs)) ->
    forall l, is_list A PA l -> P l.
```

## derive.eqcorrect

Correctness of equality test using reified type information.

```coq
Elpi derive.eqcorrect list.
Check list_eq_correct. (*
  forall A f l, is_list A (eq_axiom A f) l -> eq_axiom (list A) (list_eq A f) l
*)
```

## derive.eqOK

Correctness of equality test.

```coq
Elpi derive.eqOK list.
Check list_eq_OK. (*
  forall A f, (forall a, axiom A f a) -> (forall l, eq_axiom (list A) (list_eq A f) l)
*)
```

## Coverage

```coq
Inductive empty := .
Inductive unit := tt.
Inductive peano := Zero | Succ (n : peano).
Inductive option A := None | Some (_ : A).
Inductive pair A B := Comma (a : A) (b : B).
Inductive seq A := Nil | Cons (x : A) (xs : seq A).
Inductive rose (A : Type) := Leaf | Node (sib : seq (rose A)).
Inductive nest A := NilN | ConsN (x : A) (xs : nest (pair A A)).
Fail Inductive bush A := BNil | BCons (x : A) (xs : bush (bush A)).
Inductive w A := via (f : A -> w A).
Inductive vect A : peano -> Type := VNil : vect A Zero | VCons (x : A) n (xs : vect A n) : vect A (Succ n).
Inductive dyn := box (T : Type) (t : T).
Inductive zeta Sender (Receiver := Sender) := Envelope (a : Sender) (ReplyTo := a) (c : Receiver).
Inductive beta (A : (fun x : Type => x) Type) := Redex (a : (fun x : Type => x) A).
Inductive iota := Why n (a : match n in peano return Type with Zero => peano | Succ _ => unit end).
Inductive large := K1 (_ : unit) | K2 (_ : unit) (_ : unit) | ...
```

test   | eq      | param1  | map     | induction | param1P | isK     | projK   | bcongr  | eqK     | eqcorrect | eqOK
-------|---------|---------|---------|-----------|---------|---------|---------|---------|---------|-----------|--------
empty  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
unit   | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
peano  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
option | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
pair   | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
seq    | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
rose   | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
nest   | :cloud: | :sunny: | :cloud: | :sunny:   | :cloud: | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:
w      | :cloud: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:
vect   | :sunny: | :sunny: | :sunny: | :sunny:   | :cloud: | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:
dyn    | :cloud: | :sunny: | :sunny: | :sunny:   | :bug:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:
zeta   | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:
beta   | :bug:   | :sunny: | :bug:   | :sunny:   | :bug:   | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:
iota   | :bug:   | :sunny: | :sunny: | :sunny:   | :bug:   | :sunny: | :sunny: | :cloud: | :bug:   | :bug:     | :bug:
large  | :sunny: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny:
