Require Import Arith List FunctionalExtensionality.
From elpi Require Import elpi.
Require Import ZArith.

Lemma ring_example x : x + 1 = 1 + x.
Proof. ring. Qed.

Goal forall l, map (fun x => x + 1) l = map (fun x => 1 + x) l.
Proof.
Fail replace (x + 1) with (1 + x) by ring.
replace (fun x => x + 1) with (fun x => 1 + x).
easy.
extensionality x.
ring.
Qed.

Elpi Tactic show.
Elpi Accumulate lp:{{

pred process i:list argument, o:string.

process [open-trm K_ T] S :-
coq.term->string T S.

process [trm T] S :-
coq.term->string T S.

solve (goal Ctx _Trigger Type Proof Args) _ :-
% process Args Txt,
coq.say "Goal:" Ctx "|-" Proof ":" Type ">->" Args.

}}.

Elpi Typecheck.

Ltac prove_by_extensionality_and_ring term1 term2 :=
replace term1 with term2;[ |
let Var_name := fresh "mame_for_bound_variable" in
extensionality Var_name; try ring
].

Elpi Tactic replace.

Elpi Accumulate lp:{{

pred mk-equality i:list prop, i:term i:A, o:term, o:A.
:name "mk-equality:start"
mk-equality _Ctx X A Y A :- name X, !, {{@refl_equal _ lp:X}} = Y, !.
mk-equality _Ctx (global _ as C) A C {{@refl_equal _ lp:C}} :- !.
mk-equality _Ctx (pglobal _ _ as C) A C {{@refl_equal _ lp:C}} :- !.
mk-equality _Ctx (sort _ as C) A C {{@refl_equal _ lp:C}} :- !.
mk-equality Ctx (fun N T F as C) A {{@refl_equal _ lp:C}} A :-
@pi-decl N T x\ mk-equality [decl x N T | Ctx] (F x) A1 {{@refl_equal _ _}} _A2,!.
mk-equality Ctx (fun N T F) A (fun N T1 F1) A1 :- !,
@pi-decl N T x\ mk-equality [decl x N T | Ctx] (F x) A (F1 x) A1.
mk-equality Ctx (let N T B F as C) A {{@refl_equal _ lp:C}} A :-
mk-equality Ctx B A {{@refl_equal _ _}} A2,
(@pi-decl N T x\ mk-equality [def x N T B | Ctx] (F x) A2 {{@refl_equal _ _}} _A3),!.
mk-equality Ctx (let N T B F) A (let N T1 B1 F1) A3 :- !,
mk-equality Ctx B A B1 A2,
@pi-decl N T x\ mk-equality [def x N T B | Ctx] (F x) A2 (F1 x) A3.
mk-equality Ctx (prod N T F) A (fun N T F1) A2 :- !,
(@pi-decl N T x\ mk-equality [decl x N T | Ctx] (F x) A1 (F1 x) A2).
mk-equality Ctx (app L as C) A {{@refl_equal _ lp:C}} A :-
std.fold-map L A (mk-equality Ctx) L1 _A1,
std.forall L1 (c \ c = {{@refl_equal _ _}}),!.
mk-equality Ctx (app L) A (app L1) A1 :- !,
std.fold-map L A (mk-equality Ctx) L1 A1.
mk-equality Ctx (fix N Rno Ty F as C) A {{@refl_equal _ lp:C}} A :- !.
mk-equality Ctx (match T Rty B as C) A {{@refl_equal _ lp:C}} A3 :- !.
mk-equality _Ctx (primitive _ as C) A {{@refl_equal _ lp:C}} A :- !.
mk-equality Ctx (uvar M L as C) A {{@refl_equal _ lp:C}} A :- !.
% when used in CHR rules
mk-equality Ctx (uvar X L as C) A {{@refl_equal _ lp:C}} A :- !.

pred fold-map-ctx-item i:prop,  i:A, o:prop,o:A.
fold-map-ctx-item (decl X N T) A (decl X1 N T1) A2 :- fold-map X A X1 A1, fold-map T A1 T1 A2.
fold-map-ctx-item (def X N T B) A (def X1 N T1 B1) A3 :-
  fold-map X A X1 A1, fold-map T A1 T1 A2, fold-map B A2 B1 A3.

pred fold-map-arity i:arity,  i:A, o:arity, o:A.
fold-map-arity (parameter ID IMP T R) A (parameter ID IMP T1 R1) A2 :-
  fold-map T A T1 A1, pi x\ fold-map-arity (R x) A1 (R1 x) A2.
fold-map-arity (arity T) A (arity T1) A1 :- fold-map T A T1 A1.

pred process i:argument, i:argument, i:term, o:term, o:term.

% The header says we want to replace a formula with one unknown
% by a formula with also one unknown in the Goal.
process (open-trm 1 (fun Name _Ty F1))    % to be replaced
        (open-trm 1 (fun _Name1 _Ty1 F2)) % to be inserted in place
        GoalConcl                         % term in which to replace
        FirstLambda                       % Lambda to replace
        (fun Name2 Ty2 H'):-              % lambda to insert in place

% The 1 in first and second arguments expresses there is exactly one
% unknown in these terms (expected to be the same unknown, not checked here
% We expect the unknown to be instantiated by a bound variable in
% the first lambda in the goal.  We perform the replacement in that lambda
% without checking that there is progress (in this preliminary version).

% We look for lambdas in the goal.  Behware that
% TopLambdas contains the expressions in reverse order of their
% discovery in a left-to-right traversal.
%  std.do! [
    ((pi T A T\ fold-map T A T [T | A] :- T = (fun _ _ _)) =>
      fold-map GoalConcl [] _ TopLambdas),
    MSG is "variable " ^ {coq.name->id Name} ^ " is unknown",
% We take the first lambda
    std.assert! ({std.rev TopLambdas} = [FirstLambda | _]) MSG,
    FirstLambda = (fun Name2 Ty2 H),
% We perform the required replacement in the body of the lambda
    (pi C \ copy (F1 C) (F2 C) => copy (H C) (H' C))
  %]
  .

% Accepting the case where the replacement term does not contain the
% unknown variable present in the replaced term.
process (open-trm 1 (fun Name Ty F1)) (trm T) GConcl L1 L2:-
  coq.say "second rule",
  process (open-trm 1 (fun Name Ty F1)) (open-trm 1 (fun Name Ty (C \ T)))
  GConcl L1 L2.


solve (goal _ _ Type _ [Arg1, Arg2] as G) GL :-
    process Arg1 Arg2 Type Term1 Term2,
    std.assert! (coq.ltac.call "prove_by_extensionality_and_ring"
        [trm Term1, trm Term2] G GL) "ltac call failed".

solve (goal _ _ _ _ [Arg1, Arg2]) _ :-
  coq.say Arg1,
  coq.say Arg2,
  fail.
}}.

Elpi Typecheck.

Goal forall l, map (fun x => (x + 1) + 2) l = map (fun x => (1 + x) + 2) l.
Proof.
now intros l; elpi replace (x + 1) (1 + x).
Qed.

(* This is a typical bigop theorem. *)
Lemma fold_neutral {A B : Type}(f : A -> A -> A) (a0 : A) :
  (forall x, f x a0 = x) ->
  forall (l : list B), fold_right f a0 (map (fun _ => a0) l) = a0.
Proof.
intros neutral; induction l as [ | b l Ih]; simpl; try rewrite Ih; auto.
Qed.


Open Scope Z_scope. (* Otherwise ring fails. *)
Goal forall l, fold_right Z.add 0 (map (fun x => x - x) l) = 0.
Proof.
elpi replace (x - x) (0).
apply (fold_neutral Z.add 0 Z.add_0_r).
Qed.
