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

  solve [goal Ctx Solution T _] _.

  typecheck.
".

Elpi Tactic intro "

  solve [goal Ctx Solution Type _Attributes] [str Name] :-
    coq-evd-print,
coq-string->name Name N,
    Ctx => of (lam N hole x\ hole) Type Solution.

".

Elpi Tactic refl "

  solve [goal Ctx Solution Type _Attributes] _ :-
    Ctx => of {{refl_equal _}} Type Solution.

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
  Ctx => (pi x\ decl x `f` T => (sigma H HT\
    coq-elaborate (B x) (B1 x) (Ty x),
    coq-elaborate (G x) (G1 x) (GTy x),
    coq-say [B,B1,Ty,G,G1,GTy],
    {rev Ctx} = [decl X _ _|_],
    coq-elaborate {{lp:X = 2}} H HT,
    coq-say [H,HT]
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

solve [goal C Ev T _] [str Msg, trm X] :-
  coq-say Msg X,
  C => of X T R,
  Ev = R.

".

Section T1.
Variable a : nat.


Lemma test_elab2 T (f : forall x :nat, T x) x : forall g, (forall y, g y a) -> g (f x) a.
Proof.
intros g H.
elpi test.args.exact "this" (H _).
Qed.
 
  
Elpi Tactic ltac "

  pred read-evar i:term, o:goal.

  constraint evar pp decl def read-evar {
    rule (Ctx ?- evar (?? as X) Ty RX)
       \ (read-evar (?? as Y) G)
       > X ~ Y
      <=> (G = goal Ctx X Ty []).
  }

  type nabla (term -> goal) -> goal.
  pred distribute i:(term -> list goal), o:list goal.
  distribute (_\ []) [].
  distribute (x\ [X x| XS x]) [nabla X|R] :- distribute XS R.

  pred apply i:list goal, i:(goal -> list goal -> prop), o:list goal.
  apply [G|Gs] Tac O :-
    enter G Tac O1, apply Gs Tac O2, append O1 O2 O.
  apply [] _ [].

  pred enter i:goal, i:(goal -> list goal -> prop), o:list goal.
  enter (nabla G) T O :- (pi x\ enter (G x) T (NG x)), distribute NG O.
  enter (goal _ _ _ _ as G) T O :- T G O.

  pred collect-goals i:term, o:list goal.
  collect-goals (app L) GSS :- map L collect-goals GS, flatten GS GSS.
  collect-goals (?? as X) [G] :-
    declare_constraint (read-evar X G) [X].
  collect-goals (lam _ T F) GS :-
    collect-goals T GT,
    (pi x\ collect-goals (F x) (GF x), distribute GF GSF),
    append GT GSF GS.
  collect-goals _ [].  % TODO: finish

  pred refine i:term, i:goal, o:list goal.
  refine T (goal Ctx Ev Ty _) GS :-
    Ctx => of T Ty R, Ev = R, collect-goals Ev GS.

  assumption (goal [decl X _ _|C] X _ _) [].
  assumption (goal [def  X _ _ _ _|C] X _ _) [].
  assumption (goal [_|C] X _ _) [] :- assumption (goal C X _ _) [].

  pred constructor i:goal, o:list goal.
  constructor (goal Ctx Ev Ty _ as G) GS :-
    whd Ty [] (indt GR) Args,
    coq-env-indt GR _ _ _ _ Ks Kt,
    exists2 Ks Kt (k\ t\ refine {saturate t k} G GS).

  pred intro i:@name, i:goal, o:list goal.
  intro N G GS :- refine (lam N hole x\ hole) G GS.

  pred saturate i:term, i:term, o:term.
  saturate Ty T O :- whd Ty [] (prod _ Src Tgt) [], !, mk-app T [hole] R, pi x\ saturate (Tgt x) R O.
  saturate _ X X.

  try T G GS :- T G GS.
  try _ G [G].
  repeat T G GS :- T G GS1, apply GS1 (repeat T) GS.
  repeat _ G [G].

  or TL G GS :- exists TL (t\ t G GS).

  solve [G] [] :- repeat (or [constructor, intro `foo`, assumption]) G _.

  typecheck.
".

Require Vector.

Lemma test_elab3 : Vector.t nat 1 * True * (True -> False -> True -> False).
Proof.
elpi query "typecheck".
repeat elpi ltac.
Qed.

Print test_elab3.

End T1.


