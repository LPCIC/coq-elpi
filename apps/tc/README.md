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
}.
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
of $c_0$ and $c_1$). Then the application of `«Eqb»` is used to create the head of 
the clause with its arguments and `eqProd`, the gref of the current instance, 
is used as the solution of the current goal applied to all of the quantified 
variables.

The set of rules allowing to compile instances in elpi are grouped in 
[compiler.elpi](elpi/compiler.elpi).

### Instance priorities

To reproduce coq behavior, instances need to respect a notion of priority:
sometime multiple instances can be applied on a goal, but, for sake of
performances, the order in which they are tried is essential. 

In the previous example, the goal `Eqb ?V` where `?V` is a meta-variable, it 
is important to first use the rules `eqBool` and then `eqProd`, the latter 
causing an infinite loop. 

In elpi, we have the possibility to create rules with names and, then, new rules
can be added with respect to a particular grafting (see
[here](https://github.com/FissoreD/coq-elpi/blob/a11558758de0a1283bd9224b618cc75e40f118fb/coq-builtin.elpi#L1679)). 

Our strategy of instance insertion in the elpi database reposes on a predicate
`pred hook o:string` having, by default, $1.001$ implementations each of them
having a name going from `"0"` to `"1000"` (bounds included). Roughly what we
have is the following:

```prolog
:name "0" hook "0".
:name "1" hook "1".
...
:name "999" hook "999".
:name "1000" hook "1000".
```

In this way an instance can be added at the wanting position to respect its
priority. In particular, the priority of an instance can be defined in two
different ways by the user by coq and we retrieve this piece of
information via the `Event` listener from `coq` (see
[here](https://github.com/coq/coq/blob/f022d5d194cb42c2321ea91cecbcce703a9bcad3/vernac/classes.mli#L81)).
This event contains either a class or an instance and in the latter case we can
get its priority (see
[here](https://github.com/FissoreD/coq-elpi/blob/a11558758de0a1283bd9224b618cc75e40f118fb/apps/tc/src/coq_elpi_tc_register.ml#L57)).

#### Technical details

1. If the instance has no user defined priority, the attribute containing the
   priority of the instance is set to `None`. In this case, the priority is
   computed as the number of premises the instance has. For example, `eqBool`
   has priority $2$, since it has two hypothesis triggering recursive instance
   search.
2. If $P$ is the priority of both the instance $I_1$ and the instance $I_2$ of 
   a class $C$, then the instance that should be tried before is the one which
   has been defined later (this is coq default behavior). To respect this order,
   the grafting we use is `after P` for both instances, in this way, elpi will
   put the second-defined instance before the first one.
3. The number of hook in elpi is bounded to $1.000$, it is however possible to
   extend it via the command `Elpi AddHook G OldName NewName` where `G` is
   either after or before and `NewName` is the new hook that will be grafted
   after\before the hook called `OldName`. For instance, `Elpi AddHook after
   1000 1002` creates a hook named `1002` after `1000` and `Elpi AddHook before
   1002 1001` insert the hook `1001` before `1002`. Note that `OldName` should
   be an existing name, otherwise, a blocking error will be thrown at the next 
   invocation of an elpi code.
4. The event listener for instance and class creation can be extended with new
   elpi programs via the command `Elpi Register TC Compiler PROG`, where `PROG`
   is the name of the new elpi program called by the `Event` listener of coq. 
   Note that in the case of the creation of a 
   - Type class $C$, `PROG` is called with `[str C]` as argument where `C` is the 
     name of the class 
   - Instance $I$, `PROG` is called with `[str I, str C, str Loc, int Prio]`
     where `I` is the name of the instance, `C` the name of the class it
     implements, `Loc` is its `Locality` (one among `Local`, `Global`, `Export`)
     and `Prio` is its priority.
     
   The default elpi program for instance and class insertion is called 
   `auto_compiler` (see [here](https://github.com/FissoreD/coq-elpi/blob/a11558758de0a1283bd9224b618cc75e40f118fb/apps/tc/theories/tc.v#L61))

## Goal resolution

The resolution of type class goals is done via the `TC_solver` tactic (see
[here](https://github.com/FissoreD/coq-elpi/blob/d674089e5f5773d5d922f185e2ff058e595fa8b8/apps/tc/theories/tc.v#L29)).
This tactic 


<!-- Talk about class_hacked.ml and class_takeover.ml -->

## Commands

<details>
  <summary><code>print_instances</code> (click to expand)</summary><p>

</details>

<details>
  <summary><code>set_deterministic</code> (click to expand)</summary><p>

</details>

<details>
  <summary><code>get_class_info</code> (click to expand)</summary><p>

</details>

## Options

## Other 

## Features

### Classic vs Deterministic search

## WIP

<!-- Talk about event register. instances are re-added on section end -->
<!-- Custom rules -->
<!-- 
  Modes 
  Say that instance search is well suited for elpi since it is based on prologish search style 
-->

