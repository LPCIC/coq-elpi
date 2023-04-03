From elpi.apps.tc Require Import compiler.
From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
  inj x y : S (f x) (f y) -> R x y.
Elpi Override TC TC_check Inj.
Require Import Lia.

Generalizable All Variables.

Definition g x := x + 1.
Definition f (x: nat) := x.

Axiom eq1 : relation nat.
Axiom eq2 : relation nat.
Axiom eq3 : relation nat.

Lemma isInjg : Inj eq3 eq1 g. Admitted.

Lemma isInjf : Inj eq1 eq3 f. Admitted.

Lemma isInjf_old : Inj eq1 eq2 f. Admitted.
Lemma isInjg_old : Inj eq2 eq3 g. Admitted.

Lemma isInjinr {A B}: Inj eq eq (@inr A B).
Proof.
  red; intros.
  injection H.
  easy.
Qed.

Lemma isInjf_eq : Inj eq eq f.
Proof. red; intuition. Defined.

Lemma isInjg_eq : Inj eq eq g.
Proof. red; unfold g; intros [| x] [|y]; lia. Defined.

Global Existing Instance isInjf_eq.
Global Existing Instance isInjg_eq.
Global Existing Instance isInjf.
Global Existing Instance isInjg.
Global Existing Instance isInjf_old.
Global Existing Instance isInjg_old.
Local Instance id_inj {A} : Inj eq eq (@id A).
Admitted.
Local Instance inl_inj {A B} : Inj eq eq (@inl A B).
Admitted.
Local Instance inr_inj {A B} : Inj eq eq (@inr A B).
Admitted.

Definition compose {T1 T2 T3: Type} (g: T2 -> T3) (f : T1 -> T2) (x: T1) := g(f x).
Local Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f).
Admitted.

Elpi add_instances "instances" isInjf_eq isInjg_eq.
Elpi Print TC_check.
(* Elpi add_instances Inj. *)

Check (_ : Inj _ _ (compose g f)).

Elpi add_instances Inj.

(* Elpi Debug "debug" "debug ctx->clause" "show-tc-test".  *)

Goal forall (T1 T2 : Type) (f: T1 -> T2) (x : bool), 
  let r := Inj eq eq f in 
  let x := true in
  (if x then r else r) -> r -> Inj eq eq f -> Inj eq eq f.
  intros.
  simpl in H.
  Check (_ : Inj _ _ f).
Admitted.

Goal forall (T1 T2 : Type) (f: T1 -> T2), 
  let r := Inj eq eq f in 
  let b := true in 
  let cond := (match b with 
    | true => r 
    | false => f = f end) in 
  cond -> Inj eq eq f.
  intros.
  unfold cond in H.
  simpl in H.
  unfold r in H.
  Check (_ : Inj _ _ f).
Admitted.

Section testInj.
  Context (f : nat -> nat -> nat) `{!Inj eq eq f}.

  Local Instance xxx : Inj eq eq (compose f (Nat.add 3)).
  Admitted.

  Elpi add_instances Inj.
  Check (_ : Inj _ _ f).
  
  Elpi Print TC_check.
End testInj.

Elpi Print TC_check.

Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.

Local Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 ff} y : Inj R1 R3 (λ x, ff x y).
Admitted.

Global Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 ff} x : Inj R2 R3 (ff x).
Admitted.

Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  solve (goal Ctx _ Ty Sol _ as G) GL :-
    var Sol,
    % Add's the section's definition to the current context
    % in order to add its TC if present
    std.map {coq.env.section} (x\r\ sigma F\ coq.env.typeof (const x) F, r = (decl (global (const x)) _ F)) SectionCtx,
    ctx->clause {std.append Ctx SectionCtx} Clauses,
    Clauses => if (tc Ty X) 
      (
        refine X G GL ; 
        coq.say "illtyped solution:" {coq.term->string X}
      ) 
      (GL = [seal G]).
}}.
Elpi Typecheck TC_check.

Elpi Accumulate tc.db lp:{{
  :after "complexHook"
  tc {{ Inj _ _ lp:{{app L}} }} S :- 
    L = [_, _, _ | _],
    std.last L Last,
    std.drop-last 1 L Firsts,
    tc {{Inj _ _ lp:{{app [app Firsts, Last]}}}} S.
}}.
Elpi Typecheck TC_check.

Elpi add_instances Inj Inj2.
Elpi Typecheck TC_check.

Goal Inj2 eq eq eq Nat.add -> Inj eq eq (Nat.add 0).
intros.
apply _.
Qed.

Generalizable All Variables.
Class Equiv A := equiv: relation A.

Goal Inj2 eq eq eq Nat.add -> Inj eq eq (fun x => Nat.add x 0).
intros.
apply _.
Qed.

(* Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  tc A B :-
    coq.say "A" A "B" B "End", fail.
 }}.
Elpi Typecheck TC_check. *)

(* Elpi Accumulate tc.db lp:{{
  :after "complexHook"
  tc {{ Inj _ _ lp:{{app L}} }} S :- 
    L = [_, _, _ | _],
    std.last L Last,
    std.drop-last 1 L Firsts,
    S = {{@inj2_inj_2 _ _ _ _ _ _ lp:{app Firsts} _ lp:Last}}.
}}.
Elpi Typecheck TC_check. *)


(* Elpi Accumulate tc.db lp:{{
  pred prod-len i:term, o:int.
  prod-len (prod _ _ E) R :-
    pi x\ sigma X\ prod-len (E x) X, R is X + 1.
  prod-len _ 1.
  pred give-len i:term.
  give-len (prod Name Ty Cnt) :-
    prod-len Ty Len,
    coq.say Name Len,
    pi x\ give-len (Cnt x).
  give-len _.

  pred compile2 i:term, i:term, i:list (list prop), i:list term, o:prop.
  compile2 (prod _ T F) CT ListRHS ListVar (pi x\ C x) :-
    prod-len T Len,
    coq.say Len,
    pi p\ sigma L\

      compile2 (F p) CT L [p | ListVar] (C p).
  compile2 _ I ListRHS ListVar (tc Ty AppInst :- RevRHS) :- 
    AppInst = app [I | {std.rev ListVar}],
    std.rev ListRHS RevRHS.
}}.
Elpi Typecheck TC_check. *)

Elpi Query TC_check lp:{{
  coq.locate "Inj" X,
  const C = X,
  coq.env.const C _ R.
  % give-len R.
}}.

Definition p (T : Type) := @pair T T.

Elpi Print TC_check.
Goal forall (T1 T2: Set), Inj2 eq eq eq (@p nat) -> Inj eq eq (@p nat 0).
intros.
(* apply (inj2_inj_2 ). *)
apply _.
Qed.

(* Global Hint Mode Inj - - ! ! -: typeclass_instances.
Global Hint Mode Inj - - ! ! !: typeclass_instances. *)

(* Elpi add_instances Inj ignoreClasses Inj2 Equiv. *)
(* Elpi add_instances Inj ignoreInstances isInjf_eq. *)
(* Elpi add_instances Inj. *)
(* Elpi add_instances Inj ignoreInstances compose_inj. *)
(* Elpi add_instances instances compose_inj isInjf_eq isInjg_eq. *)
(* Elpi add_instances instances inr_inj. *)

Goal forall (A: Type) (x: A -> A), let y := Inj eq eq x in let z := y in z -> Inj eq eq (compose x x).
Proof.
  intros T x y z H.
  (* following diverges: the compiler should unfold the def *)
  (* Check (_ : Inj eq eq (compose x x)). *)
Admitted. 