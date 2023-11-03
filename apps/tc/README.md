# Type class solver

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
`coq.elpi.add-predicate` API) a new predicate called `tc-Path.tc-ClassName` with
$N + 1$ terms where:

- `Path` is the is the logical path in which the type class `ClassName` is
  located
- $N$ is the number of parameter of the `ClassName`. In particular, if a type
  class $C$ as the parameters $P_1,\dots, P_n$ then the corresponding predicate
  will have $N$ parameters of type `term` ($1$ per parameter) and a last
  parameter in output mode containing the result of the instance search.
  By default, all the first $P_1,\dots,P_n$ parameters are in output mode.  

The set of rules allowing to add new type-class predicates in elpi are grouped
in [create_tc_predicate.elpi](elpi/create_tc_predicate.elpi).

### Deterministic search 

Sometimes, it could be interesting to disable the backtracking search for some
type classes, for performances issues or design choices. In coq the flag
*Typeclasses Unique Instances* (see
[here](https://coq.inria.fr/refman/addendum/type-classes.html#coq:flag.Typeclasses-Unique-Instances))
allows to block any kind of a backtrack on instance search: in this case type
classes are supposed to be canonical.

In the example below, we want the `NoBacktrack` type class not to backtrack if 
a solution is found.

```coq
Class NoBacktrack (n: nat).
Elpi set_deterministic NoBacktrack.
(* Ideally
       #[backtrack(off)] Class NoBacktrack (n : nat).
 *)
Class A (n: nat).

Instance a0 : A 0. Qed.
Instance nb0 : NoBacktrack 0. Qed.
Instance nb1 : NoBacktrack 1. Qed.
Instance a3 n : NoBacktrack n -> A n -> A 3. Qed.

Goal A 3. Fail apply _. Abort.
```

The goal `A 3` fails since the only instance matching it is `a3`, but we are not 
able to satisfy both its premises. In particular, the instance `nb1` is applied 
first, which fixes the parameter `n` of `a3` to `1`. Then the algorithm tries to 
find a solution for `A 1` (the second premise), but no implementation of `A` can 
solve it. In the classic approach, the type class solver would backtrack on the 
premise `NoBacktrack n` and try to apply `nb0` (this would find a solution), but 
since the type class `NoBacktrack` is deterministic, then `nb0` is discarded.

In this implementation, the elpi rule for the instance `a3` is:

```elpi 
  tc-A {{3}} {{a3 lp:A lp:B lp:C}} :-
    do-once (tc-NoBacktrack A B), 
    tc-A A C.
```

The predicate `do-once i:prop` has 

```prolog
do-once P :- P, !.
```

as implementation. The cut (`!`) operator is in charge to avoid backtracking on 
the query `tc-NoBacktrack A B`

### Instance compilation

Instances are compiled in elpi from their type. In particular, since the
$\forall$-quantification and the left hand side of implications of coq are both
represented with the `prod` type in elpi, we can say that the type of an
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
****
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
4. The event listener for instance/class creation can be extended with new
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
5. A registered event listener for instance/class can be deactivated, activated
   respectively with 
   1. `Elpi TC Activate Observer PROG.`
   2. `Elpi TC Deactivate Observer PROG.`

    by default, once registered, the elpi program `PROG` is activated

### Instance locality

The instances in the elpi database respect the locality given by the user. This
is possible thanks to the attributes from
[here](https://github.com/FissoreD/coq-elpi/blob/ac036a71f359bc1c1ee3893949d3371df10b0aef/coq-builtin.elpi#L355).
When an instance is created the `Event` listener transfer the locality of the
instance to the elpi program in charge to make the insertion (see
[here](https://github.com/FissoreD/coq-elpi/blob/ac036a71f359bc1c1ee3893949d3371df10b0aef/apps/tc/elpi/compiler.elpi#L154)
and
[here](https://github.com/FissoreD/coq-elpi/blob/ac036a71f359bc1c1ee3893949d3371df10b0aef/apps/tc/src/coq_elpi_tc_register.ml#L37)).

As a small remark, we should consider that instances depending on section
variables should be *recompiled* on section end in order to abstract them.
In the example below

```coq 
Section Foo.
  Variable (A B: Type) (HA : Eqb A) (HB : Eqb B).
  Global Instance eqProd' : Eqb (A * B) := {...}.

  Elpi print_instances eqb.
  (* Here the elpi database has the instances HA, HB and eqProd' *)
  (* 
    And the rules for eqProd' is 
        tc-Eqb {{prod A B}} {{eqProd'}}.

     Remark: Here A and B are not elpi variables, but the coq variables from the
          context
  *)
End Foo.

Elpi print_instances eqb.
(* 
  Here HA and HB are removed since local to Foo and 
  eqProd' has been recompiled abstracting and A, B, HA and HB. They are now
  arguments of this instance
*)
(*
  The new rules for eqProd' is now 
  tc-Eqb {{prod lp:A lp:B}} {{eqProd' lp:A lp:B lp:HA lp:HB}} :-
    tc-Eqb A HA, tc-Eqb B HB.

  Remark: Here A and B are elpi variables and HA, PB are the proof that we can 
          prove {{Eqb lp:A}} and {{Eqb lp:B}}
*)
```

Concretely, in a section, we consider all instances as **local** in elpi. On
section end, the `Event` listener for instance creation triggers a new call to
the elpi program for instance compilation. This trigger contains the same event
as the one for the instance creation, but now elpi is capable to compile the
instance abstracting the section variable. Finally, if we are not in a section,
instance locality will depend on the "real" locality of that instance:

1. If the instance is *local*, then we accumulate the attribute *@local! =>*
2. If the instance is *global*, then we accumulate the attribute *@global! =>*
3. If the instance is in *export* mode, then we pass no attribute, since by default, 
   elpi rules have this particular locality


## Goal resolution

The resolution of type class goals is done via the `TC_solver` tactic (see
[here](https://github.com/FissoreD/coq-elpi/blob/d674089e5f5773d5d922f185e2ff058e595fa8b8/apps/tc/theories/tc.v#L29)
and [here](elpi/solver.elpi)). This tactic take the goal and start by
introducing the quantified variables if any, then it compiles the hypotheses
whose type is a type class and finally start by solving the goal by looking for
the instances in the elpi database. Note that the tactic, per se, is not
complicated since the search of instances is based on a DFS backtracking on
failure which is the builtin search mode of query resolution in elpi.

The elpi tactic can be called by the classic `elpi TC_solver` on the current
goal, however, this can be done implicitly done using the classic tactics of coq
doing type class resolution. In particular, we want to make our solver and coq
one coexist. The user may whish the elpi solver to solve `Only` goals concerning
particular type classes (for example, those defined in its library) and leave
coq to solve the other otherwise. To do so we can call the command `Elpi
Override TC TC_solver Only Eqb` which activates the resolution of goal of goal
concerning `Eqb` which the solver `TC_solver`. Note that multiple solvers can be
created and activated to solve different tasks. To do so, we take advantage of
the `Typeclasses.set_solve_all_instances` function from coq (see
[here](https://github.com/coq/coq/blob/f022d5d194cb42c2321ea91cecbcce703a9bcad3/pretyping/typeclasses.mli#L141))
which allows to set a solver to be called on type class goals. We have taken the
file [`classes.ml`] from
[here](https://github.com/coq/coq/blob/f022d5d194cb42c2321ea91cecbcce703a9bcad3/vernac/classes.ml#L1)
and slightly modified the function
[`resolve_all_evars`](https://github.com/FissoreD/coq-elpi/blob/17d1f20d3d4f37abfeee7edcf31f3757fd515ff3/apps/tc/src/coq_elpi_class_tactics_hacked.ml#L1165).
Now that function, before solving a goal verifies if the current goal contains
only type classes overriden by the user and if so, it uses the elpi solver for
its resolution, otherwise, it calls the default coq solver. Note that the choice
of using elpi or coq solver is done
[here](src/coq_elpi_class_tactics_takeover.ml). Moreover, we provide different 
commands to

1. Override all type class goals and solve them by the solver of elpi, that
   command is `Elpi Override TC TC_solver All`.
2. Override only some type classes, that command is `Elpi Override TC TC_solver
   Only ClassQualid+` where `ClassQualid+` is a non empty list of type class
   names. A valid call to this command is, for example, `Elpi Override TC
   TC_solver Only Eqb Decidable`.
3. Override no type class, *i.e.* solve all goals with coq solver with the
   command `Elpi Override TC TC_solver None`.
4. Blacklist some type classes from elpi solver, `Elpi Override TC -
   ClassQualid+`. For instance `Elpi Override TC TC_solver Only Eqb Decidable.
   Elpi Override TC - Decidable` in equivalent to `Elpi Override TC TC_solver
   Only Eqb`.
5. Add type classes to be solved by the solver of elpi `Elpi Override TC +
   ClassQualid+`. For instance, `Elpi Override TC TC_solver Only Eqb. Elpi
   Override TC + Decidable` is equivalent to `Elpi Override TC TC_solver Only
   Eqb Decidable`.

All of these commands are meant to dynamically change the resolution of type
classes goal in `.v` files.

## Commands 

A small recap of the available elpi commands: 

<details>
  <summary>
    <code>print_instances</code> (click to expand)
  </summary>
  
  This commands prints the list of instances inside the elpi database grouped by 
  type class and in order of priority. Note that custom rules will not appear 
  in this list. This command can also be called with the name of a type class 
  to print only the implementation of that type class in elpi. An example of the 
  result for the command `Elpi print_instance Eqb.`

  ```
  Instances list for const «Eqb» is:
    const «eqBool»
    const «eqProd»
  ```

</details>

<details>
  <summary>
    <code>set_deterministic</code> (click to expand)
  </summary>

  Take the name of a type class in parameter and sets the search mode of that 
  class to deterministic (see [here](#deterministic-search))

</details>

<details>
  <summary>
    <code>get_class_info ClassName</code> (click to expand)
  </summary>

  Prints the name of the predicate associated to the class `ClassName` 
  and its search mode (`deterministic|classic`). This command is useful 
  especially when you want to add a new custom rule for a goal resolution and 
  want to know the name of the predicate of the targeted class. 

  Example:

  ```coq
  Elpi get_class_info Eqb.

  (* Output:
    The predicate of indt «Eqb» is tc-Eqb and search mode is classic *)
  ```

</details>

**Note:** in a new library you may wish to automatically compile into your elpi
database the existing classes and instances on which you library depends. To 
do so, the $4$ following commands may be useful:

- `AddAllClasses`: look for all the defined classes and creates their predicate
- `AddClasses ClassName+`: compile the predicate for the classes in argument
- `AddAllInstances`: look for all the defined instances and compile them 
- `AddInstances InstName+`: compiles al the instances passed in argument
  
**Note:** it is important to create the predicate of type classes (if not already done)
before the insertion of instances otherwise this would throw an exception.

## Flags

Here the list of the flags available (all of them are `off` by default):

<details>
  <summary>
    <code>TC IgnoreEtaReduction</code> (click to expand)
  </summary>

  Solves the goal ignoring eta-reduction, in that case it will no longer possible 
  to unify `fun x => F x` with `F`
</details>

<details>
  <summary>
    <code>TC ResolutionTime</code> (click to expand)
  </summary>

  Print the time taken to solve a goal by looking into the set of rules in the 
  database of elpi
</details>

<details>
  <summary>
    <code>TC NameShortPath</code> (click to expand)
  </summary>

  Experimental and discouraged, it can be used to compile the predicate of type
  classes without putting the `tc-Path.` prefix before `tc-ClassName` (see
  [here](#class-compilation)). For example, the type class `Decidable` from
  `Coq.Classes` is compiled into the predicate
  `tc-Coq.Classes.DecidableClass.tc-Decidable`. For small tests, if you want a
  predicate called simply `tc-Decidable` you can either use the namespace of
  elpi (see
  [here](https://github.com/LPCIC/elpi/blob/master/ELPI.md#namespaces)) or
  activate the option `NameShortPat` which creates the predicate with the 
  short name `tc-Decidable`
</details>

<details>
  <summary>
    <code>TC TimeRefine</code> (click to expand)
  </summary>

  Prints the time taken by coq to refine the elpi solution in to the coq term
</details>

<details>
  <summary>
    Experimental: <code>TC CompilerWithPatternFragment</code> (click to expand)
  </summary>

  Compile instances using the pattern fragment unification of elpi: the coq
  term applications (`app [HD | TL]`) are replaced with the elpi application
  `(HDe TLe)` where `HDe` is the elpi representation of `HD` (similarly for `TLe`) 
</details>


## WIP

1. Mode management: 
   - Classes with a single user defined should be taken into account to use the 
    elpi modes
   - Classes with multiple modes ??
2. Clarify pattern fragment unification 
3. Topological sort of premises in modes are activated 
4. Option to disable auto compiler (maybe)

