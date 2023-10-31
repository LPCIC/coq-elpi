# Type classes 

This folder contains an alternative implementation of a type class solver for
coq written in elpi. This solver is composed by two main parts, the **compiler**
and the **solver**. The former takes coq classes and instances and "translates"
them into the elpi representation, whereas the latter is the elpi tactic aiming
to make instance search on coq goals.

## The compiler

In our implementation by compiler we mean the set of rules abstracting coq
terms, *1.* classes and *2* instances, in the elpi world. In the next two
paragraphs, we briefly explain these two phases of the compilation, where,
intuitively, a type class can be seen as a prolog predicate and the instances of
a type class $C$ as rule (clause or fact) of the elpi predicate for $C$.

For instance, if 

```coq
Class Eqb (T: Type) := {
  eqb : T -> T -> bool; 
  eq_leibniz : forall (A B: T), eqb A B = true -> A = B
}
```

is the type class representing the leibniz equality between two objects of type 
$T$, and 

```coq
Program Instance eqBool : Eqb bool := {
  eqb A B := if A then B else negb B
}.
Next Obligation. now intros [] []. Qed.
```

is an implementation of `Eqb` for the type `bool`, their corresponding elpi
representation will be:

```prolog 
  pred tc-Eqb i:term, o:term.
  tc-Eqb {{bool}} {{eqBool}}.
```

### Class compilation

The compilation of a type class creates dynamically (thanks to the
`coq.elpi.add-predicate` API) a new predicate called `tc-Path.tc-ClassName` with $N + 1$ terms where:

- `Path` is the is the logical path in which the type class `ClassName` is
  located
- $N$ is the number of parameter of the `ClassName`. In particular, if a type
  class $C$ as the parameters $P_1,\dots, P_n$ then the corresponding predicate
  will have $N$ parameters of type `term` ($1$ per parameter) and a last
  parameter in output mode containing the result of the instance search.
  By default, all the first $P_1,\dots,P_n$ parameters are in output mode.  

The set of rules allowing to add new type-class predicates in elpi are grouped
in [create_tc_predicate.elpi](elpi/create_tc_predicate.elpi)

### Instance compilation

Instances are compiled in elpi from their type. In particular, since the $\forall$-quantification and the left hand side of implications of coq are
both represented with the `prod` type in elpi, we can say that the type of an 
instance $I$ is essentially a tower of 

<pre>
prod N_1 T_1 (x_1\ 
  prod N_2 T_2 (x_2\ 
    ... 
      prod N_n T_n (x_n\ 
        app [global GR, A_1, A_2, ... A_M])))
</pre>

where $\forall i \in [1, N],\ T_i$ is the type of the quantified variable $x_i$.
Each $x_1$ represents a premise $P$ of the current instance and, if its type
$T_i$ is a type class, then $P$ is recursively compiled and added to the final
clause as a premise. The last `prod` contains `app [global GR, A_1, ..., A_M]`
where `GR` is the gref of the type class implemented by $I$ and each $A_j$ is an
argument applied to `GR` which sees every $x_i$. Note that during the
compilation of the instance the binders $x_i$ are recursively replaced by fresh
`pi` elpi variables.

For example, the instance `eqBool` showed before, has type 

`Eqb bool`, it has no quantified variable and it is directly compiled in the 
clause `tc-Eqb {{bool}} {{eqBool}}`.

On the other hand, if we take the instance below, 

```coq
Instance eqProd (A B: Type) : Eqb A -> Eqb B -> Eqb (A * B) := { ... }
```

we see that its type is 

``` 
prod `A` (sort (typ eqProd.u0»)) c0 \
 prod `B` (sort (typ eqProd.u1»)) c1 \
  prod `H0` (app [global (indt «Eqb»), c0]) c2 \
   prod `H1` (app [global (indt «Eqb»), c1]) c3 \
    app [global (indt «Eqb»), app [global (indt «prod»), c0, c1]]
```

there are in fact four variables that produce the elpi clause:

```
pi x0 x1 x2 x3\ 
  tc-Eqb {{prod lp:A lp:B}} Sol :- 
    tc-Eqb A S1, tc-Eqb B S2, 
    Sol = {{eqProd lp:A lp:B lp:S1 lp:S2}}.
```

the four variable $c_0,...,c_3$ are quantified with `pi`, the two premises
`H0` and `H1` are compiled as premises of the current goal (we need to find a 
proof that there exists an implementation of the class `Eqb` for the types 
of `c0` and `c1`). Then the application of `«Eqb»` is used to create the head of 
the clause with its arguments and `eqProd`, the gref of the current instance, 
is used as the solution of the current goal applied to all of the quantified 
variables.

The set of rules allowing to add compile instances in elpi are grouped in 
[compiler.elpi](elpi/compiler.elpi).


### Instance priorities

## Goal resolution

<!-- Talk about class_hacked.ml and class_takeover.ml -->

## Commands

## Options

## Other 

## WIP

<!-- Talk about event register -->
<!-- Custom rules -->
<!-- 
  Modes 
  Say that instance search is well suited for elpi since it is based on prologish search style 
-->

