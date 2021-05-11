# Derive

The `derive` command automatically synthesizes a bunch of useful lemmas
given an inductive type declaration.

## In a nutshell

```coq
From elpi.apps Require Import derive.

derive Inductive peano := Zero | Succ (p : peano).
Print peano. (* Inductive peano : Type :=  Zero : peano | Succ : peano -> peano *)
Eval compute in peano.eq Zero (Succ Zero). (* = false : bool *)
About peano.eq_OK. (* peano.eq_OK : forall s1 s2, reflect (s1 = s2) (peano.eq s1 s2) *)
```

See also [examples/usage.v](examples/usage.v)

## Documentation

The `elpi/` directory contains the elpi files implementing various automatic
derivation of terms.  The corresponding .v files, defining the Coq commands,
are in `theories/derive/`.

![Big picture](derive.svg)

See [Deriving proved equality tests in Coq-elpi: Stronger Induction Principles for
Containers](http://drops.dagstuhl.de/opus/volltexte/2019/11084/) for a
description of most of these components.

Single steps of the derivation are available as separate commands.
Only the main entry point `derive` comes with an handy syntax; the other
commands have to be invoked mentioning `Elpi` and only accept an already
declared inductive as input.

### derive.isK

Given an inductive type it generates for each constructor a function that
tests if a term is a specific constructor.

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

### derive.projK

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

If the projected argument's type depends on the value of other arguments, then it
is boxed using `existT`.
```coq
Check projcons3. (*
projcons3
     : forall (A : Type) (H : nat),
       A -> forall n : nat, Vector.t A n ->
       Vector.t A H -> {i1 : nat & Vector.t A i1}
*)
```

### injection

`injection H EqAB PL` given an equation `H` of type `EqAB` returns a list
of equations `PL`. `EqAB` is expected to be of the form `K .. = K ..` for
a constructor `K`.

coverage: does not do the smart thing when the obtained equations are like `{ i : nat & Vector.t A i } = ...` in which case, given that `nat` is `eqType` one could obtain systematically the two equalities.

### discriminate

`discriminate H EqAB G PG` given an equation `H` of type `EqAB` and
a goal `G` it provides a proof `PG`. It asserts that `EqAB` is of
the form `K1 .. = K2 ..` when `K1` is a constructor different from `K2`.

### derive.bcongr

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

### derive.eq

Generates a boolean comparison function.

```coq
Elpi derive.eq list. 
Check list_eq. (*
list_eq
     : forall A : Type,
       (A -> A -> bool) -> list A -> list A -> bool
*)
```

### derive.eqK

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

### derive.map

Map a container over its parameters. 

```coq
Elpi derive.map list.
Check list_map : forall A B, (A -> B) -> list A -> list B.
```

### derive.param1

Unary parametricity translation.

```coq
Elpi derive.param1 nat.
Print is_nat. (*
Inductive is_nat : nat -> Type :=
| is_O : is_nat 0
| is_S : forall n : nat, is_nat n -> is_nat (S n) *)
```

### derive.param1.functor

```coq
Elpi derive.param1.functor is_list.
Check is_list_functor : forall A PA QA,
  (forall x, PA x -> QA x) -> forall l, is_list A PA l -> list A QA l.
```

### derive.param1.inhab

```coq
Elpi derive.param1.inhab is_nat.
Check nat_is_nat : forall x : nat, is_nat x.
```


### derive.param1.congr

```coq
Elpi derive.param1.congr is_nat.
Check is_Succ congr : forall x (px qx : is_nat x),
  px = qx -> 
  is_Succ x px = is_Succ x qx.
```

### derive.param1.trivial

```coq
Elpi derive.param1.trivial is_nat.
Check is_nat_trivial : forall x : nat, { p : is_nat x & forall q, p = q }.
```

### derive.induction

Induction principle for `T` based on `is_T`

```coq
Elpi derive.induction list.
Check list_induction :
  forall (A : Type) (PA : A -> Type) P,
    P (nil A) ->
    (forall x : A, PA x -> forall xs, P xs -> P (cons A x xs)) ->
    forall l, is_list A PA l -> P l.
```

### derive.eqcorrect

Correctness of equality test using reified type information.

```coq
Elpi derive.eqcorrect list.
Check list_eq_correct :
  forall A f l, is_list A (eq_axiom A f) l -> eq_axiom (list A) (list_eq A f) l.
```

### derive.eqOK

Correctness of equality test.

```coq
Elpi derive.eqOK list.
Check list_eq_OK :
  forall A f, (forall a, axiom A f a) -> (forall l, eq_axiom (list A) (list_eq A f) l).
```

### derive.lens
See also [theories/derive/lens.v](theories/derive/lens.v) for the `Lens` definition and the support constants `view`, `set` and `over`.
```coq
Elpi derive.lens pa_record.
Check _f3 : forall A, Lens (pa_record A) (pa_record A) peano peano. 
```

### derive.lens_laws
See also [theories/derive/lens_laws.v](theories/derive/lens_laws.v) for the statements of the 4 laws (set_set, view_set, set_view, exchange).
```coq
Elpi derive.lens_laws pa_record.
Check _f3_view_set : forall A (r : pa_record A) x, view _f3 (set _f3 x r) = x.
```

### Coverage

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
Inductive prim_int := PI (i : Int63.int).
Inductive prim_float := PF (f : PrimFloat.float).
Record fo_record := { f1 : peano; f2 : unit; }.
Record pa_record A := { f3 : peano; f4 : A; }.
Record pr_record A := { pf3 : peano; pf4 : A; }. (* with primitive projections *)
Record dep_record := { f5 : peano; f6 : vect unit f5; }.
Variant enum := E1 | E2 | E3.
```

test       | eq      | param1  | map     | induction | isK     | projK   | bcongr  | eqK     | eqcorrect | eqOK    | lens_laws
-----------|---------|---------|---------|-----------|---------|---------|---------|---------|-----------|---------|----------
empty      | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
unit       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
peano      | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
option     | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
pair       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
seq        | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
rose       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
nest       | :cloud: | :sunny: | :cloud: | :sunny:   | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:   | :cloud:
w          | :cloud: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:   | :cloud:
vect       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:   | :cloud:
dyn        | :cloud: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:   | :cloud:
zeta       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
beta       | :sunny: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :bug:     | :sunny: | :cloud:
iota       | :cloud: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :cloud: | :bug:   | :cloud:   | :cloud: | :cloud:
large      | :sunny: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
prim_int   | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
prim_float | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :cloud:   | :cloud: | :cloud:
fo_record  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny:
pa_record  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny:
pr_record  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny:
dep_record | :bug:   | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:   | :cloud:  
enum       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:


test      | functor | inhab   | congr     | trivial |
----------|---------|---------|-----------|---------|
is_empty  | :sunny: | :sunny: | :sunny:   | :sunny: |
is_unit   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_peano  | :sunny: | :sunny: | :sunny:   | :sunny: |
is_option | :sunny: | :sunny: | :sunny:   | :sunny: |
is_pair   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_seq    | :sunny: | :sunny: | :sunny:   | :sunny: |
is_rose   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_nest   | :bug:   | :bug:   | :cloud:   | :cloud: |
is_w      | :bug:   | :sunny: | :sunny:   | :bug:   |
is_vect   | :sunny: | :bug:   | :cloud:   | :bug:   |
is_dyn    | :sunny: | :cloud: | :cloud:   | :bug:   |
is_zeta   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_beta   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_iota   | :sunny: | :bug:   | :cloud:   | :bug:   |
is_large  | :sunny: | :sunny: | :bug:     | :bug:   |
prim_int  | :sunny: | :sunny: | :sunny:   | :sunny: |
prim_float| :sunny: | :sunny: | :sunny:   | :sunny: |
fo_record | :sunny: | :sunny: | :sunny:   | :sunny: |
pa_record | :sunny: | :sunny: | :sunny:   | :sunny: |
pr_record | :sunny: | :sunny: | :sunny:   | :sunny: |
dep_record| :sunny: | :bug:   | :sunny:   | :bug:   |
enum      | :sunny: | :sunny: | :sunny:   | :sunny: |
