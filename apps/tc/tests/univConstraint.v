From Coq Require Export List.
From elpi.apps Require Export compiler.
Global Generalizable All Variables.

Elpi Override TC TC_solver All.

Class ElemOf A B := elem_of: A -> B -> Prop.
Class Elements A C := elements: C -> list A.

Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here (x : A) l : elem_of x (x :: l)
  | elem_of_list_further (x y : A) l : elem_of x l -> elem_of x (y :: l).
Global Existing Instance elem_of_list.

Elpi AddInstances ElemOf.

Inductive NoDup {A} : list A -> Prop :=
  | NoDup_nil_2 : NoDup nil
  | NoDup_cons_2 x l : not (elem_of x l) -> NoDup l -> NoDup (x :: l).

Module A.
  Class FinSet A C `{ElemOf A C,Elements A C} : Prop := {
    NoDup_elements (X : C) : @NoDup A (elements X)
  }.

  Fail Class FinSet1 A C `{ElemOf A C,Elements A C} : Prop := {
    NoDup_elements (X : C) : NoDup (elements X)
  }.
End A.

Module B.

  Elpi Accumulate TC_solver lp:{{
    :after "first"
    msolve L N :- !,
      coq.ltac.all (coq.ltac.open solve) L N.

    pred sep.
    sep :- coq.say "----------------".

    :after "first"
    solve1 (goal Ctx _ Ty Sol _ as G) _L GL :-
      not (Ty = prod _ _ _), var Sol,
      ctx->clause Ctx Clauses, Ty = app [global TC | _],
      @redflags! coq.redflags.beta => coq.reduction.lazy.norm Ty Ty1,
      Clauses => if (tc-search-time TC Ty1 X) 
        (
          (copy A A :- var A => copy X X_),
          coq.say "X" X "X_" X_,
          my-refine X G GL; 
          coq.say "illtyped solution:" {coq.term->string X}
        ) 
        (GL = [seal G]).
  }}.
  Elpi Typecheck TC_solver.
  
  (* Class IgnoreClass.
Elpi Override TC TC_solver Only IgnoreClass.
Set Typeclasses Debug. *)
(* Elpi Trace Browser. *)
  Class FinSet2 A C `{ElemOf A C, Elements A C} : Prop := {
    elem_of_elements2 (X : C) x : iff (elem_of x (elements X)) (elem_of x X);
    NoDup_elements2 (X : C) : @NoDup A (elements X)
  }.

(* 
1: looking for (ElemOf ?A (list ?A0)) with backtracking
1.1: simple apply @elem_of_list on (ElemOf ?A (list ?A0)), 0 subgoal(s)

2: looking for (Elements ?A C) with backtracking
2.1: exact H0 on (Elements ?A C), 0 subgoal(s)

3: looking for (ElemOf A C) without backtracking
3.1: exact H on (ElemOf A C), 0 subgoal(s)
--------------------------------------------------------------------------
1: looking for (Elements A C) without backtracking
1.1: exact H0 on (Elements A C), 0 subgoal(s)
*)
End B.