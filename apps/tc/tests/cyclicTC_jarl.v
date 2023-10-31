From elpi.apps Require Import tc.
Elpi Debug "simple-compiler".
Set TC NameShortPath.

Elpi Override TC TC_solver All.

Class A (T1 : Type).
Class B (T1 : Type).

Global Instance instA' (T1 : Type) (T2 : Type) : A bool. Qed.
Global Instance instA (T1 : Type) `(B T1) : A T1. Qed.

Global Instance instB (T1 : Type) `(A T1) : B T1. Qed.
Global Instance instB' : B nat . Qed.

Elpi Accumulate tc.db lp:{{
  pred explored_gref o:gref.

  pred should_fail i:list gref, i:gref, i:gref. 
  should_fail [] _ _. 
  should_fail [Current | Tl] Current BlackElt :- !,
    if (std.mem Tl BlackElt) fail true.
  should_fail [_ | Tl] Current BlackElt :- !, 
    should_fail Tl Current BlackElt.

  pred already_explored i:gref, i:gref. 
  already_explored Current BlackElt :- 
    std.findall (explored_gref _) As, 
    std.map As (x\r\ x = explored_gref r) As',
    should_fail As' Current BlackElt.

  pred get_other i:gref, o:gref.

  pred under_extra i:gref, i:list prop, o:list prop.
  under_extra A B C :- std.map B (x\r\ (explored_gref A => x) = r) C1,
  C = [sigma x\ get_other A x, already_explored A x | C1].

  :after "firstHook"
  make-tc IsHead Ty Inst Hyp Clause :- !,
    app [global TC | TL] = Ty,
    gref->string-no-path TC TC_Str,
    std.append TL [Inst] Args, 
    coq.elpi.predicate TC_Str Args Q,
    if (not IsHead) (Hyp = Hyp') (under_extra TC Hyp Hyp'),
    Clause = (Q :- Hyp').
}}.
Elpi Typecheck TC_solver.

Elpi AddAllClasses.
Elpi AddAllInstances.

Elpi Command AddRecursivelyDependantTC.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main [trm (global A), trm (global B)] :- 
    coq.elpi.accumulate _ "tc.db" 
      (clause _ _ (get_other A B)),
    coq.elpi.accumulate _ "tc.db" 
      (clause _ _ (get_other B A)).
  main L :- coq.say L.
}}.
Elpi Typecheck.

Elpi AddRecursivelyDependantTC (A) (B).

Elpi Bound Steps 10000.
Check (_ : B bool).
Check (_ : A nat).

