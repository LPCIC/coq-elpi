From elpi Require Import elpi.

Elpi Command foo.
Elpi Print foo.
Elpi Tactic foobar.
Elpi Print foobar.


Section foo.

Variables n m : nat.
Let o := m.

Elpi Tactic print.goal.
Elpi Accumulate lp:{{

  solve _ [goal L _ T As] _ :-
    print_constraints,
    coq.say "Goal: ", coq.say As, coq.say "\n",
    coq.say L,
    coq.say "------------",
    L => coq.say T {coq.term->string T}.

}}.

Elpi Typecheck.


Lemma test_print (T : Type) (x : forall y : T, Type) (h : o = m) (w : T) :
  forall e : x w = Type, forall j : x w, exists a : x w, a = a.
Proof.

 elpi print.goal.

 elpi print.goal.

 intros; unshelve(eexists ?[foo]); shelve_unifiable.

 elpi print.goal.

 all: cycle 1; elpi print.goal; shelve_unifiable.

 exact (refl_equal j).
Qed.

End foo.

Elpi Tactic id.
Elpi Accumulate lp:{{

  solve _ [goal _Ctx _Solution _T _] _.

}}.
Elpi Typecheck.

Elpi Tactic intro.
Elpi Accumulate lp:{{

  solve  [str Name] [goal Ctx Solution Type _Attributes] _ :-
    % coq.sigma.print,
    coq.string->name Name N,
    Ctx => of (fun N Src_ Tgt_) Type Solution.

}}.
Elpi Typecheck.

Elpi Tactic refl.
Elpi Accumulate lp:{{

  solve _ [goal Ctx Solution Type _Attributes] [] :-
    Ctx => of {{refl_equal _}} Type Solution.

}}.
Elpi Typecheck.

Lemma test_tactics (T : Type) (x : T) : forall e : x=x, e = e.
Proof.
  elpi  id.
  elpi intro "elpi_rocks". 
  elpi refl.
Qed.

(* An assignement of a term containing a hole: of is triggered
   and puts a typing constraint on FRESH_ *)

Elpi Tactic sloppy.
Elpi Accumulate lp:{{

  solve _ [goal _ S Ty _] _ :-
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
  

Elpi Tactic test.elaborate_in_ctx.
Elpi Accumulate lp:{{

solve _ [goal Ctx _Ev (prod _ T x\ app[G x,B x,_]) _] _ :-
  Ctx => (pi x\ decl x `f` T => (sigma H HT\
    coq.elaborate (B x) (Ty x) (B1 x),
    coq.elaborate (G x) (GTy x) (G1 x),
    coq.say [B,B1,Ty,G,G1,GTy],
    {std.rev Ctx} = [decl X _ _|_],
    coq.elaborate {{lp:X = 2}} HT H, % X is restricted wrt x
    coq.say [H,HT]
)).
}}.
Elpi Typecheck.
Elpi Print test.elaborate_in_ctx.

Section T.
Variable a : nat.
Lemma test_elab T (f : forall x :nat, T x) x : forall g, g (f x) a.
Proof.
elpi test.elaborate_in_ctx.
Abort.

End T.


(* Arguments *)

Elpi Tactic test.args.exact.
Elpi Accumulate lp:{{

solve [str Msg, int N, trm X] [goal C Ev T _] _ :-
  coq.say Msg N X T,
  Ev = X.

}}.

Section T1.
Variable a : nat.


Lemma test_elab2 T (f : forall x :nat, T x) x : forall g, (forall y, g y a) -> g (f x) a.
Proof.
intros g H.
Check 1356.
elpi test.args.exact "this" 3 (H _).
Qed.
 

End T1.


