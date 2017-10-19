From elpi Require Import elpi.

Section foo.

Variables n m : nat.
Let o := m.

Elpi Tactic print.goal "

  solve [goal L X T As] _ :-
    coq-say ""Goal: "", coq-say As, coq-say ""\n"",
    coq-say L,
    coq-say ""------------"",
    coq-say {pp T},
    coq-say {{n + m + o}}.

  typecheck.

".


Lemma test_print (T : Type) (x : forall y : T, Type) (h : o = m) (w : T) :
  forall e : x w = Type, forall j : x w, exists a : x w, a = a.
Proof.

 elpi query print.goal "typecheck".

 elpi print.goal.

 elpi print.goal.

 intros; unshelve(eexists ?[foo]); shelve_unifiable.

 elpi print.goal.

 all: cycle 1; elpi print.goal; shelve_unifiable.

 exact (refl_equal j).
Qed.

End foo.

Elpi Tactic id "

  solve [goal _ Solution T _] _ :- Solution = hole.
".

Elpi Tactic intro "

  solve [goal _ Solution Type _Attributes] [str Name] :-
    coq-string->name Name N,
    Solution = lam N hole x\ hole.

".

Elpi Tactic refl "

  solve [goal _ Solution Type _Attributes] _ :-
    Solution = {{refl_equal _}}.

".
 
Lemma test_tactics (T : Type) (x : T) : forall e : x=x, e = e.
Proof.
  elpi id.
  elpi intro "elpi_rocks". 
  elpi refl. 
Qed.

(* A wrong implementation of a tactic that does not
   declare _FRESH in the constraint set as a typed evar,
   hence Coq can't read the term back *)

Elpi Command wrong.
Elpi Accumulate " 

  solve [goal _ S _ _] :-
    S = app[{{S}}, _FRESH],
    evar _X {{nat}},
    evar _XX {{nat -> bool}},
    print_constraints.

".

Lemma wrong : nat.
Proof.
  Fail elpi wrong.
Abort.



Elpi Tactic test.elaborate_in_ctx.
Elpi Accumulate "

solve [goal Ctx Ev (prod _ T x\ app[G x,B x,_]) _] _ :-
  (pi x\ decl x `f` T => (sigma H HT\
    coq-elaborate (B x) (B1 x) (Ty x),
    coq-elaborate (G x) (G1 x) (GTy x),
    coq-say [B,B1,Ty,G,G1,GTy],
    {rev Ctx} = [decl X _ _|_],
    coq-elaborate {{lp:X = 2}} H HT,
    coq-say [H,HT]
)),
  Ev = hole.
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

solve [goal _ Ev _ _] [str Msg, trm X] :- coq-say Msg X, Ev = X.

".

Section T1.
Variable a : nat.


Lemma test_elab2 T (f : forall x :nat, T x) x : forall g, (forall y, g y a) -> g (f x) a.
Proof.
intros g H.
elpi test.args.exact "this" (H _).
Qed.

 
Elpi Tactic ltac "

  ltac-idtac [goal _ Solution _ _ as G] [G] :- Solution = hole.

  ltac-intro [goal Ctx Solution Goal A] (str Name) K :-
    coq-string->name Name N,
    (of (lam N hole x\ hole) Goal Solution1),
    Solution1 = (lam _ T G), Solution = Solution1,
    (unify-eq Goal (prod _ _ TG)),
    (pi x\ decl x N T => K [goal [decl x N T|Ctx] (G x) (TG x) []]).

  ltac-intros G [] K :- K G.
  ltac-intros G [N|NS] K :- ltac-intro G N (g\ ltac-intros g NS K).

  ltac-exact N [goal Ctx Solution _ _] [] :- nth N Ctx (decl Solution _ _).

  ltac-stop _ _.

  flatten [] [].
  flatten [X|XS] L :- flatten XS L1, append X L1 L.

  tclTHEN T1 T2 G NGS :- T1 G NG, map NG (g\ T2 [g]) NGSL, flatten NGSL NGS.

  solve G A :- ltac-intros G A (g\ coq-evd-print, ltac-exact 0 g _), coq-evd-print.

  typecheck.
".

Lemma test_elab3 T (f : forall x :nat, T x) x : forall g, (g (f x) a) -> g (f x) a.
Proof.
elpi query "typecheck".
elpi ltac g H.
Qed.

End T1.


