From elpi Require Import elpi.

Elpi Tactic double_open.
Elpi Accumulate lp:{{
  solve (goal _Ctx _Trigger Type _Proof [] as G) GL :-
    (@no-tc! ==> refine {{ id _ }} G [G2]),
    coq.ltac.open (refine {{ id _ }}) G2 GL,
    coq.say G2.
}}.


Lemma foo (P : Prop) :
P -> P.
Proof.
  elpi double_open.
  match goal with |- P -> P => idtac end. (* no renaming *)
Abort.

Elpi Command foo.
Elpi Print foo "elpi.tests/foo".
Elpi Tactic foobar.
Elpi Print foobar "elpi.tests/foobar".



Elpi Tactic print_goal.
Elpi Accumulate lp:{{

  solve (goal L _ T _ As as G) [seal G] :-
    print_constraints,
    coq.say "Goal: ", coq.say As, coq.say "\n",
    coq.say L,
    coq.say "------------",
    coq.say T {coq.term->string T}.

}}.



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


Elpi Tactic intro.
Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [str Name] as G) GS :-
    coq.string->name Name N,
    refine (fun N Src_ Tgt_) G GS.

}}.


Elpi Tactic refl.
Elpi Accumulate lp:{{

  solve (goal _Ctx Solution _ _ _) [] :-
    Solution = {{refl_equal _}}.

}}.


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


Definition one : nat.
Proof.
  elpi sloppy.
  exact 0.
Defined.
Check eq_refl : one = 1.
  

Elpi Tactic test_typecheck_in_ctx.
Elpi Accumulate lp:{{

solve (goal Ctx _Ev (prod _ T x\ app[G x,B x,_]) _ _) _ :-
  pi x\ decl x `f` T ==> sigma H HT\
    coq.typecheck (B x) (Ty x) ok,
    coq.typecheck (G x) (GTy x) ok,
    coq.say [B,Ty,G,GTy],
    Ctx = [decl X _ _|_],
    H = {{lp:X = 2}},
    coq.typecheck H HT ok, % X is restricted wrt x
    coq.say [H,HT]
.
}}.

Elpi Print test_typecheck_in_ctx "elpi.tests/test_typecheck_in_ctx".

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

solve (goal _ Ev T _ [str Msg, int N, trm X, str Q]) _ :-
  coq.say Msg N X T Q,
  Ev = X.

}}.


Section T1.
Variable a : nat.


Lemma test_elab2 T (f : forall x :nat, T x) x : forall g, (forall y, g y a) -> g (f x) a.
Proof.
intros g H.
Check 1356.
elpi test_args_exact "this" 3 (H _) foo.bar .
Qed.
 

End T1.

(* purity of tactics *)

Elpi Tactic test_impure.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ []) _ :-
  coq.env.add-const "xxx" _ {{ nat }} _ _.

}}.


Lemma test_impure : True.
Proof.
Fail elpi test_impure.
Abort.

(* ltac notations *)

Elpi Tactic test.notation.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ A) _ :- coq.say A, print_constraints.

}}.


Tactic Notation "test_cl" constr_list(X) := elpi test.notation ltac_term_list:(X).
Tactic Notation "test_ocl" open_constr_list(X) := elpi test.notation ltac_term_list:(X).
Tactic Notation "test_ucl" uconstr_list(X) := elpi test.notation ltac_term_list:(X).
Tactic Notation "test_hl" hyp_list(X) := elpi test.notation ltac_term_list:(X).

Tactic Notation "test_c" constr(X) := elpi test.notation ltac_term:(X).
Tactic Notation "test_oc" open_constr(X) := elpi test.notation ltac_term:(X).
Tactic Notation "test_uc" uconstr(X) := elpi test.notation ltac_term:(X).
Tactic Notation "test_h" hyp(X) := elpi test.notation ltac_term:(X).
Tactic Notation "test_i" int(X) := elpi test.notation ltac_int:(X).
Tactic Notation "test_i2" integer(X) := elpi test.notation ltac_int:(X).
Tactic Notation "test_s" string(X) := elpi test.notation ltac_string:(X).
Tactic Notation "test_s2" ident(X) := elpi test.notation ltac_string:(X).
Tactic Notation "test_s3" hyp(X) := elpi test.notation ltac_string:(X).

Tactic Notation "legacy_test_c" constr(X) := elpi test.notation (X).
Tactic Notation "legacy_test_oc" open_constr(X) := elpi test.notation (X).
Tactic Notation "legacy_test_uc" uconstr(X) := elpi test.notation (X).
Tactic Notation "legacy_test_h" hyp(X) := elpi test.notation (X).


Lemma test_notation (x y : nat) : True.
Proof.

test_cl x (x + y).
Fail test_cl x (_ + y).
test_ocl x (_ + y).
test_ucl x (_ + y).
test_hl x y.

test_c (x + y).
Fail test_c (_ + y).
test_oc (_ + y).
Fail test_oc (0 0).
test_uc (_ + y).
test_uc (0 0).
test_h x.
Fail test_h z.
test_i 1.
test_i2 -1.
test_s "a".
test_s2 a.
test_s3 x.
Fail test_s3 z.

legacy_test_c (x + y).
Fail legacy_test_c (_ + y).
legacy_test_oc (_ + y).
legacy_test_uc (_ + y).
legacy_test_h x.
Fail legacy_test_h z.

Abort.


Elpi Tactic test_sideeff.
Elpi Accumulate lp:{{
  pred myexists i:goal, o:list sealed-goal.
  myexists (goal _ RawEv _ Ev _) GS1 :-
    RawEv = {{ ex_intro (fun x : nat => x = 1) _ _ }},
    coq.ltac.collect-goals Ev GS Shelved,
    std.append GS Shelved GS1,
    std.assert! (std.length GS1 2) "not 2 goals".

  pred myrefl i:goal, o:list sealed-goal.
  myrefl (goal _ _ _ P _ as G) GL :-
    std.assert! (var P) "second goal was not skipped",
    refine {{ eq_refl _ }} G GL.

  solve G GL :-
    coq.ltac.thenl [coq.ltac.open myexists, coq.ltac.open myrefl] (seal G) GL.
}}.


Goal exists x, x = 1.
elpi test_sideeff.
Abort.

Elpi Tactic test_att.
Elpi Accumulate lp:{{
  solve _ _ :-
  coq.say "YYYYYYYYYYYYYYYYYYYYYYYYYYYY" {attributes},
    coq.parse-attributes {attributes} [ att "foo" bool, att "bar" bool ] Opts,
    coq.say "XXXXXXXXXXXXXXXXXXXXXXXXXXX" Opts,
    (Opts ==> get-option "foo" tt).
}}.


Tactic Notation "#[" attributes(A) "]" "testatt" := ltac_attributes:(A) elpi test_att.
Tactic Notation "testatt" "#[" attributes(A) "]" := ltac_attributes:(A) elpi test_att.

Goal True.
(#[ foo ] testatt).
idtac; #[ foo ] testatt.
Fail (#[ bar ] testatt).
Fail (#[ foo2 ] testatt).
testatt #[ foo ].
Abort.

(* ***************** *)

Elpi Tactic test.m.
Elpi Accumulate lp:{{
  type type-arg open-tactic.
  type-arg (goal _ _ _ _ [trm T|_] as G) GL :-
    refine T G GL.
  type-arg (goal A B C D [X|R]) GL :-
    coq.say "skip" X,
    type-arg (goal A B C D R) GL.

  msolve GL New :- coq.say {attributes},
    coq.ltac.all (coq.ltac.open type-arg) GL New.
}}.


Goal (forall x : nat, x = x) /\ (forall x : bool, x = x).
split; intro x.
all: elpi test.m (@eq_refl _ x).
Qed.

Elpi Query lp:{{
  coq.notation.add-abbreviation-for-tactic "XX.xxx" "test.m" [int 1, str "33", trm {{bool}}]
}}.

Print Grammar constr.

Goal (forall x : nat, x = x) /\ (forall x : bool, x = x).
split; intro x.
all: exact (XX.xxx (@eq_refl _ x)).
Qed.

Check forall xxx : nat, forall XX : bool, True.

Elpi Export test.m.

Goal (forall x : nat, x = x) /\ (forall x : bool, x = x).
split; intro x.
all: exact (test.m (@eq_refl _ x)).
Qed.

Set Warnings "-non-reversible-notation".
Notation Foo pp := ltac:(elpi test.m (pp)).

Goal (forall x : nat, x = x) /\ (forall x : bool, x = x).
split; intro x.
all: exact (Foo (@eq_refl _ x)).
Qed.

Tactic Notation "Bar" open_constr(pp) :=
  elpi test.m (pp).
Notation Bar qq := ltac:(Bar (@eq_refl _ qq)).

Goal (forall x : nat, x = x) /\ (forall x : bool, x = x).
split; intro x.
all: exact (Bar x).
Qed.

Elpi Tactic t.
Elpi Accumulate lp:{{
  solve G _ :- coq.say G.
}}.


Tactic Notation "t1" constr(h) := idtac h.
Tactic Notation "t2" constr(h) := elpi t ltac_term:(h).
Section Test.
  Hypothesis H : True.
  Lemma foo : True.
  Proof.
    t1 H. (* first tactic, works *)
    elpi t (H). (* expected equivalent of t2, works *)
    t2 (H = H). (* t2 called with a term containing H, works *)
    t2 H. (* called just with H, fails *)
  Abort.
End Test.

(* we test we can pass ltac values around *)

Elpi Tactic app.
Elpi Accumulate lp:{{
  solve (goal C R T P [tac F, tac X]) GL :-
    coq.ltac.call-ltac1 F (goal C R T P [tac X]) GL.
}}.


Tactic Notation "foo" simple_intropattern_list(l) :=
  elpi app ltac_tactic:(let f x := x in f) ltac_tactic:( intros l ).

Goal forall n, n + 1 = 1.
  foo [|m].
    trivial.
    match goal with |- S m + 1 = 1 => idtac end.
Abort.  



Elpi Tactic fresh1.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ forall x : lp:Ty, _ }} _ _ as G) GL :-
    coq.ltac.fresh-id "x" Ty ID,
    coq.id->name ID N,
    refine (fun N _ _) G GL.
}}.

Goal forall x z y, x = 1 + y + z.
intros x x0.
elpi fresh1.
Check x1.
Abort.

Implicit Type (w : nat).

Goal forall x z y, x = 1 + y + z.
intros ??.
elpi fresh1.
Check w.
Abort.


