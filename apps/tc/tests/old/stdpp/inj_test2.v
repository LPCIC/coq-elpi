From elpi.apps.tc Require Import compiler.
From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.
Require Import Lia.

Generalizable All Variables.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
  inj x y : S (f x) (f y) -> R x y.

Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.

Definition gInj x := x + 1 * 1.
Definition fInj (x: nat) := x * 3 * 2.
Axiom eq1 : relation nat.
Axiom eq2 : relation nat.
Axiom eq3 : relation nat.
Local Instance isInjg : Inj eq3 eq1 gInj. Admitted.
Local Instance isInjf : Inj eq1 eq3 fInj. Admitted.
Local Instance isInjf_old : Inj eq1 eq2 fInj. Admitted.
Local Instance isInjg_old : Inj eq2 eq3 gInj. Admitted.
Lemma x A B: Inj eq eq (@inr A B). Admitted.
Local Instance isInjf_eq : Inj eq eq fInj. Admitted.
Local Instance isInjg_eq : Inj eq eq gInj. Admitted.

Local Instance id_inj {A} : Inj eq eq (@id A). Admitted.
Local Instance inl_inj {A B} : Inj eq eq (@inl A B). Admitted.
Local Instance inr_inj {A B} : Inj eq eq (@inr A B). Admitted.

Definition compose {T1 T2 T3: Type} (g: T2 -> T3) (f : T1 -> T2) (x: T1) := g(f x).
Local Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f).
Admitted.

Elpi AddInstances Inj.


Elpi Accumulate TC_solver lp:{{
  pred gref->redflag i:gref, o:coq.redflag.
  gref->redflag (const C) (coq.redflags.const C).

  pred find-term i:goal-ctx, i:term, o:term.
  find-term [] A A.
  find-term [def A _ _ B | _] A B.
  find-term [_ | A] T R :- find-term A T R.

  pred simpl-term i:goal-ctx, i:term, o:term.
  simpl-term Ctx (app L) (app Res) :-
    std.map L (simpl-term Ctx) Res.
  simpl-term Ctx (match T P Br) (match T' P' Br') :-
    simpl-term Ctx T T',
    simpl-term Ctx P P',
    std.map Br (simpl-term Ctx) Br'.
  simpl-term Ctx (fun N T B) (fun N T' B') :-
    simpl-term Ctx T T',
    pi x\ simpl-term Ctx (B x) (B' x).
  simpl-term Ctx (prod N T B) (prod N T' B') :-
    simpl-term Ctx T T',
    pi x\ simpl-term Ctx (B x) (B' x).
  simpl-term Ctx (let N X T B) (let N X' T' B') :-
    simpl-term Ctx T T', 
    simpl-term Ctx X X',
    pi x\ simpl-term Ctx (B x) (B' x).
  simpl-term Ctx X Y :-
    find-term Ctx X Y.

  pred reduce i:goal-ctx, o:goal-ctx.
  reduce Ctx CtxNew :-
    std.map Ctx (x\r\ sigma A B C Res Bo\ 
      ((def A B C Bo = x, r = def A B C Res); 
       (decl A B Bo = x, r = decl A B Res)), 
       simpl-term Ctx Bo Res) Res,
    % if (Res = Ctx) (CtxNew = Ctx) (reduce Ctx Res).
    CtxNew = Res.
  
  :after "hintHook"
  solve (goal Ctx _ Ty Sol _ as G) GL :- !,
  coq.say Ctx "\n",
    reduce Ctx Ctx',
    reduce Ctx' Ctx'',
    reduce Ctx'' Ctx''',
    reduce Ctx''' Ctx'''',
    reduce Ctx'''' Res,
    simpl-term Res Ty Ty',
    simpl-term Res Ty' Ty'',
    simpl-term Res Ty'' Ty''',
    var Sol,
    std.map {coq.env.section} (x\r\ sigma F\ coq.env.typeof (const x) F, r = (decl (global (const x)) _ F)) SectionCtx,

    ctx->clause {std.append Res SectionCtx} Clauses,
    Clauses => if (std.spy-do![tc Ty''' X]) 
      (
        refine X G GL ; 
        coq.say "illtyped solution:" {coq.term->string X}
      ) 
      (GL = [seal G]).
}}.
Elpi Typecheck TC_solver.

Elpi Override TC TC_solver Inj.


Goal forall (A: Type) (x: A -> A), 
  let y := Inj eq eq x in 
  let z := y in z -> Inj eq eq (compose x x).
Proof.
  intros T x y z H.
  simpl.
  unfold z in H.
  unfold y in H.
  apply _.
Admitted. 


Elpi Override TC TC_solver Inj.

Goal forall (A: Type) (x: A -> A), 
  let y := Inj eq eq x in 
  let z := y in z -> Inj eq eq (compose x x).
Proof.
  intros T x y z H.
  apply _.
Admitted. 
