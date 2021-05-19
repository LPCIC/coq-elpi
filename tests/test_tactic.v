From elpi Require Import elpi.

Elpi Command foo.
Elpi Print foo.
Elpi Tactic foobar.
Elpi Print foobar.



Elpi Tactic print_goal.
Elpi Accumulate lp:{{

  solve (goal L _ T _ As as G) [seal G] :-
    print_constraints,
    coq.say "Goal: ", coq.say As, coq.say "\n",
    coq.say L,
    coq.say "------------",
    coq.say T {coq.term->string T}.

}}.

Elpi Typecheck.

Section foo.

Variables n m : nat.
Let o := m.

Lemma test_print (T : Type) (x : forall y : T, Type) (h : o = m) (w : T) :
  forall e : x w = Type, forall j : x w, exists a : x w, a = a.
Proof.

 elpi print_goal.

 elpi print_goal.

 intros; unshelve(eexists ?[foo]); shelve_unifiable.

 elpi print_goal.

 all: cycle 1; elpi print_goal; shelve_unifiable.

 exact (refl_equal j).
Qed.

End foo.

Elpi Tactic id.
Elpi Accumulate lp:{{

  solve (goal _Ctx _Solution _T _RefinedSolution _ as G) [seal G].

}}.
Elpi Typecheck.

Elpi Tactic intro.
Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [str Name] as G) GS :-
    coq.string->name Name N,
    refine (fun N Src_ Tgt_) G GS.

}}.
Elpi Typecheck.

Elpi Tactic refl.
Elpi Accumulate lp:{{

  solve (goal _Ctx Solution _ _ _) [] :-
    Solution = {{refl_equal _}}.

}}.
Elpi Typecheck.

Lemma test_tactics (T : Type) (x : T) : forall e : x=x, e = e.
Proof.
  elpi id.
  elpi intro "elpi_rocks". 
  elpi refl.
Qed.

(* An assignement of a term containing a hole: of is triggered
   and puts a typing constraint on FRESH_ *)

Elpi Tactic sloppy.
Elpi Accumulate lp:{{

  solve (goal _ S Ty _ _) _ :-
    print_constraints,
    coq.say S Ty,
    S = app[{{S}}, FRESH_ ],
    print_constraints,
    coq.say "hello".

}}.
Elpi Typecheck.

Definition one : nat.
Proof.
  elpi sloppy.
  exact 0.
Defined.
Check eq_refl : one = 1.
  

Elpi Tactic test_typecheck_in_ctx.
Elpi Accumulate lp:{{

solve (goal Ctx _Ev (prod _ T x\ app[G x,B x,_]) _ _) _ :-
  pi x\ decl x `f` T => sigma H HT\
    coq.typecheck (B x) (Ty x) ok,
    coq.typecheck (G x) (GTy x) ok,
    coq.say [B,Ty,G,GTy],
    {std.rev Ctx} = [decl X _ _|_],
    H = {{lp:X = 2}},
    coq.typecheck H HT ok, % X is restricted wrt x
    coq.say [H,HT]
.
}}.
Elpi Typecheck.
Elpi Print test_typecheck_in_ctx.

Section T.
Variable a : nat.
Lemma test_elab T (f : forall x :nat, T x) x : forall g, g (f x) a.
Proof.
elpi test_typecheck_in_ctx.
Abort.

End T.


(* Arguments *)

Elpi Tactic test_args_exact.
Elpi Accumulate lp:{{

solve (goal _ Ev T _ [str Msg, int N, trm X]) _ :-
  coq.say Msg N X T,
  Ev = X.

}}.
Elpi Typecheck.

Section T1.
Variable a : nat.


Lemma test_elab2 T (f : forall x :nat, T x) x : forall g, (forall y, g y a) -> g (f x) a.
Proof.
intros g H.
Check 1356.
elpi test_args_exact "this" 3 (H _).
Qed.
 

End T1.

(* purity of tactics *)

Elpi Tactic test_impure.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ []) _ :-
  coq.env.add-const "xxx" _ {{ nat }} _ _.

}}.
Elpi Typecheck.

Lemma test_impure : True.
Proof.
Fail elpi test_impure.
Abort.

(* ltac notations *)

Elpi Tactic test_notation.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ A) _ :- A = [_,_], coq.say A.

}}.
Elpi Typecheck.

Tactic Notation "test" constr_list(X) := elpi test_notation ltac_term_list:(X).
Tactic Notation "test1" open_constr_list(X) := elpi test_notation ltac_term_list:(X).
Tactic Notation "test2" uconstr_list(X) := elpi test_notation ltac_term_list:(X).


Lemma test_notation (x y : nat) : True.
Proof.
test x y.
Fail test (x + _) x.
Elpi Trace 1 2.
test1 (x + _) x.
Fail test2 (x + _) x.
Abort.

