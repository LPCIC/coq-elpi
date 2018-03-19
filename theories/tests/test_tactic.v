From elpi Require Import elpi.

Elpi Command foo.
Elpi Print foo.
Elpi Tactic foobar.
Elpi Print foobar.


Section foo.

Variables n m : nat.
Let o := m.

Elpi Tactic print.goal "

  solve _ [goal L _ T As] _ :-
    coq.say ""Goal: "", coq.say As, coq.say ""\n"",
    coq.say L,
    coq.say ""------------"",
    L => coq.say {pp T},
    coq.say {{n + m + o}}.

".

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

Elpi Tactic id "

  solve _ [goal Ctx Solution T _] _.

".

Elpi Tactic intro "

  solve  [str Name] [goal Ctx Solution Type _Attributes] _ :-
    coq.evd-print,
coq.string->name Name N,
    Ctx => spy(of (lam N hole x\ hole) Type Solution).

".

Elpi Tactic refl "

  solve _ [goal Ctx Solution Type _Attributes] [] :-
    Ctx => spy(of {{refl_equal _}} Type Solution).

".

Lemma test_tactics (T : Type) (x : T) : forall e : x=x, e = e.
Proof.
  elpi  id.
  elpi intro "elpi_rocks". 
  elpi refl.
Qed.

(* A wrong implementation of a tactic that does not
   declare _FRESH in the constraint set as a typed evar,
   hence Coq can't read the term back *)

Elpi Command wrong.
Elpi Accumulate " 

  solve _ [goal _ S _ _] _ :-
    S = app[{{S}}, _FRESH],
    evar _X {{nat}},
    evar _XX {{nat -> bool}},
    coq.evd-print.

".

Lemma wrong : nat.
Proof.
  Fail elpi wrong.
Abort.



Elpi Tactic test.elaborate_in_ctx.
Elpi Accumulate "

solve _ [goal Ctx Ev (prod _ T x\ app[G x,B x,_]) _] _ :-
  Ctx => (pi x\ decl x `f` T => (sigma H HT\
    coq.elaborate (B x) (B1 x) (Ty x),
    coq.elaborate (G x) (G1 x) (GTy x),
    coq.say [B,B1,Ty,G,G1,GTy],
    {rev Ctx} = [decl X _ _|_],
    coq.elaborate {{lp:X = 2}} H HT,
    coq.say [H,HT]
)).
".
Section T.
Variable a : nat.
Lemma test_elab T (f : forall x :nat, T x) x : forall g, g (f x) a.
Proof.
elpi test.elaborate_in_ctx.
Abort.

End T.


(* Arguments *)

Elpi Tactic test.args.exact "

solve [str Msg, int N, trm X] [goal C Ev T _] _ :-
  coq.say Msg N X,
  C => of X T R,
  Ev = R.

".

Section T1.
Variable a : nat.


Lemma test_elab2 T (f : forall x :nat, T x) x : forall g, (forall y, g y a) -> g (f x) a.
Proof.
intros g H.
elpi test.args.exact "this" 3 (H _).
Qed.
 

End T1.


