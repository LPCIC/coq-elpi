From elpi.apps.tc Require Import compiler.
From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.
Require Import Lia.

Generalizable All Variables.

(* Elpi Debug "debug" "debug ctx->clause" "show-tc-test".  *)

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) :=
  inj x y : S (f x) (f y) -> R x y.
Elpi Override TC TC_check Only Inj.

Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.

Local Instance ffff: Inj eq eq (PeanoNat.Nat.succ). Admitted.

Elpi add_instances Inj. 
Check (_ : Inj _ _ PeanoNat.Nat.succ).
Check (_ : Inj _ _ S).

Definition gInj x := x + 1.
Definition fInj (x: nat) := x.

Axiom eq1 : relation nat.
Axiom eq2 : relation nat.
Axiom eq3 : relation nat.

Local Instance isInjg : Inj eq3 eq1 gInj. Admitted.

Local Instance isInjf : Inj eq1 eq3 fInj. Admitted.

Local Instance isInjf_old : Inj eq1 eq2 fInj. Admitted.
Local Instance isInjg_old : Inj eq2 eq3 gInj. Admitted.

Lemma isInjinr {A B}: Inj eq eq (@inr A B). Admitted.

Local Instance isInjf_eq : Inj eq eq fInj. Admitted.
Local Instance isInjg_eq : Inj eq eq gInj. Admitted.

Local Instance id_inj {A} : Inj eq eq (@id A). Admitted.
Local Instance inl_inj {A B} : Inj eq eq (@inl A B). Admitted.
Local Instance inr_inj {A B} : Inj eq eq (@inr A B). Admitted.

Definition compose {T1 T2 T3: Type} (g: T2 -> T3) (f : T1 -> T2) (x: T1) := g(f x).
Local Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f).
Admitted.

Elpi add_instances Inj.

Check (_ : Inj _ _ S).
Check (_ : Inj _ _ (compose gInj fInj)).

Goal forall (T1 T2 : Type) (f: T1 -> T2) (x : bool), 
  let r := Inj eq eq f in 
  let x := true in
  (if x then r else r) -> r -> Inj eq eq f -> Inj eq eq f.
  intros.
  simpl in H.
  Check (_ : Inj _ _ f).
  apply _.
Qed.

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
  apply _.
Qed.

Section testInj.
  Context (f : nat -> nat -> nat) `{!Inj eq eq f}.

  Global Instance xxx : Inj eq eq (compose f (Nat.add 3)).
  Admitted.

  Elpi add_instances Inj.
  Check (_ : Inj _ _ f).
  
  Elpi Print TC_check.
End testInj.

Elpi Print TC_check.

Print Instances Inj.

Elpi Accumulate TC_check lp:{{
  pred def2let i:goal-ctx, o:term.
  def2let [decl _Var _Name Ty] (Ty).
  def2let [(def _ Name Ty Body)| TL] (let Name Ty Body (x\ TLT)) :-
    def2let TL TLT.
  def2let [decl _Var _Name Ty | TL] (app [Ty, TLT]) :-
    def2let TL TLT.
  def2let _ _:- coq.say "not ehre", fail.

  :after "hintHook"
  solve (goal Ctx _ Ty Sol _ as G) GL :-
    var Sol,
    % Add's the section's definition to the current context
    % in order to add its TC if present
    std.map {coq.env.section} (x\r\ sigma F\ coq.env.typeof (const x) F, r = (decl (global (const x)) _ F)) SectionCtx,
    ctx->clause {std.append Ctx SectionCtx} Clauses,
    % coq.say Ctx "\n",
    % std.rev Ctx CtxRev,
    % def2let CtxRev RClauses,
    % @redflags! coq.redflags.zeta => coq.reduction.lazy.norm RClauses Y,
    % coq.say "ACCA" RClauses,
    % coq.say "BlaBB" Y,
    Clauses => if (tc Ty X) 
      (
        refine X G GL ; 
        coq.say "illtyped solution:" {coq.term->string X}
      ) 
      (GL = [seal G]).

}}.
Elpi Typecheck TC_check.

(* Elpi Query TC_check lp:{{
  X = {{let x := 1 in let y := 2 in let z := 3 in x}},
  @redflags! coq.redflags.zeta => coq.reduction.lazy.norm X Y,
  coq.say Y.
}}. *)

Goal let x := 1 in let y := 2 in let z := 3 in x = x -> Inj eq eq (Nat.mul 0) -> Inj eq eq (Nat.mul 0).
  intros.
  apply _.
Qed.

Local Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 ff} y : Inj R1 R3 (λ x, ff x y).
Admitted.

Global Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 ff} x : Inj R2 R3 (ff x).
Admitted.

Elpi add_instances Inj.

(* Elpi Print TC_check. *)

Goal Inj2 eq eq eq Nat.mul -> Inj eq eq (Nat.mul 0).
  intros.
  apply _.
Qed.

Goal Inj2 eq eq eq Nat.add -> Inj eq eq (fun x => Nat.add x 0).
intros.
apply _.
Qed.

Elpi Accumulate tc.db lp:{{
  % :before "hintHook"
  tc {{ @Inj lp:T1 lp:T2 lp:R1 lp:R3 lp:{{app L}} }} S :- 
    std.last L Last,
    coq.typecheck Last Ty ok,
    std.drop-last 1 L Firsts,
    if (Firsts = [F]) true (F = app Firsts),
    S = {{@inj2_inj_2 _ _ _ _ _ _ lp:F lp:S1 lp:Last}},
    tc {{ @Inj2 lp:Ty lp:T1 lp:T2 _ lp:R1 lp:R3 lp:F }} S1.
  }}.
Elpi Typecheck TC_check.

Definition p (T : Type) := @pair T T.
Elpi add_instances Inj.

Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  tc A _ :- coq.say "A" A, fail.
}}.
Elpi Typecheck TC_check.

Goal Inj eq eq (compose fInj gInj).
apply _.
Qed.

Elpi Accumulate tc.db lp:{{
  tc {{ Inj lp:R1 lp:R3 lp:F }} S :- 
    F = (fun _ _ _), !,
    G = {{ compose _ _ }},
    coq.unify-eq G F ok,
    tc {{ Inj lp:R1 lp:R3 lp:G }} S.
}}.

Check (_ : Inj _ _ (compose fInj gInj)).
Check (_ : Inj _ _ (fun x => fInj (gInj x))). 

Goal forall (T1 T2: Set), Inj2 eq eq eq (@pair nat T1) -> Inj eq eq (@pair nat T1 0).
intros.
apply _.
(* apply (inj2_inj_2 ). *)
Qed.

Goal forall (A: Type) (x: A -> A), let y := Inj eq eq x in let z := y in z -> Inj eq eq (compose x x).
Proof.
  intros T x y z H.
  (* apply _. *)
  (* following diverges: the compiler should unfold the def *)
  (* Check (_ : Inj eq eq (compose x x)). *)
Admitted. 

(* Global Hint Mode Inj - - ! ! -: typeclass_instances.
Global Hint Mode Inj - - ! ! !: typeclass_instances. *)

(* Elpi add_instances Inj ignoreClasses Inj2 Equiv. *)
(* Elpi add_instances Inj ignoreInstances isInjf_eq. *)
(* Elpi add_instances Inj. *)
(* Elpi add_instances Inj ignoreInstances compose_inj. *)
(* Elpi add_instances instances compose_inj isInjf_eq isInjg_eq. *)
(* Elpi add_instances instances inr_inj. *)