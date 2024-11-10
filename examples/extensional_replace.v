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

Check functional_extensionality.

Lemma let_congr {T1 T2 : Type} (b1 b2 : T1) (F1 F2 : T1 -> T2) :
  b1 = b2 -> (forall x : T1, F1 x = F2 x) ->
  (let x := b1 in F1 x) = (let x := b2 in F2 x).
Proof.
intros bq fq; rewrite bq.
lazy zeta; apply fq.
Qed.

About f_equal.
About f_equal2.
About f_equal3.

About eq_trans.
About id.

Elpi Tactic replace.

Elpi Accumulate lp:{{

pred mk-app-prf i:list term, i:list term, i: list term, o:term.

mk-app-prf [F, _] [_, _] [{{@refl_equal _ _}}, P] {{f_equal lp:F lp:P}}.
mk-app-prf [F, _, _] [_, _, _] [{{@refl_equal _ _}}, P1, P2]
  {{f_equal2 lp:F lp:P1 lp:P2}}.
mk-app-prf [F, _, _, _] [F, _, _, _] [{{@refl_equal _ _}}, P1, P2, P3]
  {{f_equal3 lp:F lp:P1 lp:P2 lp:P3}}.

pred fold-map2 i:list term i:A i:(term -> A -> term -> term -> A -> prop) 
  o:list term o:list term o:A.

fold-map2 [] A _ [] [] A.
fold-map2 [T | L] A F [T1 | L1] [P1 | PL] A2 :-
  F T A T1 P1 A1, fold-map2 L A1 F L1 PL A2.

pred instantiate_pair i:name, i:term, i:term, i:pair argument argument,
    o:pair argument argument.

pred instantiate i:name, i:term, i:term, i:argument, o:argument.

pred remove_one_unknown i:name, i:term, i:term, i:term, o:term.

remove_one_unknown N _T C (fun N1 _T1 F) Res :-
  {coq.name->id N} = {coq.name->id N1},!,
 
  Res = (F C),!,
   coq.say "remove the unknown" Res.

remove_one_unknown N T C (fun N1 T1 F) (fun N1 T1 Res) :-
  coq.say "not the unknown" N N1,
  (@pi-decl N1 T1 x \ 
     remove_one_unknown N T C (F x) (Res x)),!.

instantiate N T C (open-trm 1 F) (trm Res) :-
  remove_one_unknown N T C F Res,!.

instantiate N T C (open-trm I F) (open-trm J Res) :-
  remove_one_unknown N T C F Res,!,
  J is I - 1.

instantiate _N _T _C (trm A) (trm A):- !.

instantiate_pair N T C (pr A1 A2) (pr B1 B2) :-
  std.do! [ coq.say "before" N T C A1 B1, 
  std.assert! (instantiate N T C A1 B1) "first instantiate failed",
   coq.say "between" B1, instantiate N T C A2 B2,
   coq.say "after" N T C (pr B1 B2)].

pred mk-equality i:(pair argument argument), i:term i:A, o:term, o:term, o:A.

mk-equality (pr (trm S) (trm T)) S A T {{@id (lp:S = lp:T) _}} A :- !,
  coq.say "rewrite happens".

:name "mk-equality:start"
mk-equality _Ctx X A Z Y A :- name X,!, 
coq.say "first clause", X = Z, {{@refl_equal _ lp:X}} = Y, !.
mk-equality _Ctx (global _ as C) A C {{@refl_equal _ lp:C}} A :- !,
coq.say "second clause" C.
mk-equality _Ctx (pglobal _ _ as C) A C {{@refl_equal _ lp:C}} A :- !,
coq.say "third clause".
mk-equality _Ctx (sort _ as C) A C {{@refl_equal _ lp:C}} A :- !,
coq.say "fourth clause".

mk-equality Ctx (fun N T F as C) A C Res A :-
@pi-decl N T x\
  (instantiate_pair N T x Ctx Ctx1,
   mk-equality Ctx1 (F x) A _ {{@refl_equal _ _}} _A2,!,
   Res = {{@refl_equal _ _}},
   coq.say "fifth clause").

mk-equality Ctx (fun N T F) A (fun N T F1) 
  {{functional_extensionality lp:{{(fun N T F)}} lp:{{(fun N T F1)}}
      lp:{{(fun N T Prf)}}}} A1 :- !,
      coq.say "sixth clause",
@pi-decl N T x\
  (std.assert! (instantiate_pair N T x Ctx Ctx1) "instantiate_pair failed",!,
   mk-equality Ctx1 (F x) A (F1 x) (Prf x) A1).

mk-equality Ctx (let N T B F as C) A C {{@refl_equal _ lp:C}} A :-
mk-equality Ctx B A _ {{@refl_equal _ _}} A2,
(@pi-decl N T x\
  (std.assert! (instantiate_pair N T x Ctx Ctx1) "instantiate_pair failed",!,
  mk-equality Ctx1 (F x) A2 _ {{@refl_equal _ _}} _A3)),!,
  coq.say "seventh clause".

mk-equality Ctx (let N T B F) A (let N T B1 F1) 
  {{let_congr lp:B lp:B1 lp:{{fun N T F}} lp:{{fun N T F1}}
      lp:PB lp:PF}} A3:- !,
mk-equality Ctx B A B1 PB A2,
@pi-decl N T x\ 
  (instantiate_pair N T x Ctx Ctx1,!,
  coq.say "eigth clause",
   mk-equality Ctx1 (F x) A2 (F1 x) PF A3).

mk-equality Ctx (prod N T F) A (prod N T F1) (fun N T P1) A2 :- !,
(@pi-decl N T x\ 
  (instantiate_pair N T x Ctx Ctx1,!,
   mk-equality  Ctx1 (F x) A (F1 x) (P1 x) A2)),!,
   coq.say "ninth clause".

mk-equality Ctx (app L as C) A C {{@refl_equal _ lp:C}} A :-
fold-map2 L A (mk-equality Ctx) _ L1 _A1,
std.forall L1 (c \ c = {{@refl_equal _ _}}),!,
coq.say "tenth clause".

mk-equality Ctx {{@map Z Z lp:F lp:L}} A {{@map Z Z lp:F1 lp:L1}}
  R A2 :- !,
  coq.say "eleventh clause",
   mk-equality Ctx F A F1 Pf A1,
   mk-equality Ctx L A1 L1 Pl A2,!,
   R = {{f_equal2 (@map Z Z) lp:Pf lp:Pl}}.
   
mk-equality Ctx (app L) A (app L1) Prf A1 :-
% this can only succeed if the two lengths have the same length
coq.say "entering twelfth",
fold-map2 L A (mk-equality Ctx) L1 P1 A1,
coq.say "fold-map2 succeeded", !,
mk-app-prf L L1 P1 Prf.

mk-equality _Ctx (fix _N _Rno _Ty _F as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _Ctx (match _T _Rty _B as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _Ctx (primitive _ as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _Ctx (uvar _M _L as C) A C {{@refl_equal _ lp:C}} A :- !.
% when used in CHR rules
mk-equality _Ctx (uvar _X _L as C) A C {{@refl_equal _ lp:C}} A :- !.

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
  process (open-trm 1 (fun Name Ty F1)) (open-trm 1 (fun Name Ty (C \ T)))
  GConcl L1 L2.


solve (goal _ _ Type _ [Arg1, Arg2] as G) GL :-
    process Arg1 Arg2 Type Term1 Term2,
    std.assert! (coq.ltac.call "prove_by_extensionality_and_ring"
        [trm Term1, trm Term2] G GL) "ltac call failed".

solve (goal _ _ {{ _ = lp:Y }} _ [_, Arg1, Arg2] as G) GL :-
  coq.say "calling equality with " (pr Arg1 Arg2) Y,
  mk-equality (pr Arg1 Arg2) Y [] Y2 P _,
  coq.say "mk-equality succeeded" P,
  coq.typecheck P {{lp:Y = lp:Y2}} _Diag,!,
  coq.term->string Y2 S,
  coq.say "typecheck succeeded" S,
  refine {{eq_sym (@eq_trans _ _ lp:Y2 _ lp:P (eq_sym _))}} G GL.
  % refine {{eq_sym (@eq_trans lp:Y lp:Y2 lp:X lp:P (eq_sym _))}} G GL.

solve (goal _ _ _ _ [Arg1, Arg2]) _ :-
  coq.say Arg1,
  coq.say Arg2,
  fail.

solve (goal _ _ _ _ [] as _G) _GL :-
  coq.say "failed".
}}.

Elpi Typecheck.

Open Scope Z_scope.
Elpi Query lp:{{
  sigma T1 T2 A \
  {{fun x => x + (1 + 0)}} = T1,
  {{fun x => x + 1}} = T2,
  instantiate_pair `x` {{Z}} A (pr (open-trm 1 T1) (open-trm 1 T2)) R
}}.


Goal forall l, map (fun x => (x + 1) + 2) l = map (fun x => (1 + x) + 2) l.
Proof.
now intros l; elpi replace (x + 1) (1 + x).
Show Proof.
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

Goal forall x, x = 1 -> 2 = x + 1.
intros x x1.
elpi replace True (x) (1);[assumption | ].
ring.
Qed.

Goal forall l, map (fun x => x + 1) l = map (fun x => (x + (1 + 0))) l.
Proof.
intros l.
elpi replace True (x + (1 + 0)) (x + 1).

Qed.

Goal forall x, x = 1.
Proof.
intros x.
elpi replace.
