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
Fail Check f_equal6.

About eq_trans.
About id.

About map_ext_in.

Lemma map_ext_in_equal2 [A B : Type] (f g : A -> B) (l1 l2 : list A):
  (forall a : A, In a l1 -> f a = g a) -> l1 = l2 ->
  map f l1 = map g l2.
Proof.
now intros exth l1l2; rewrite <- l1l2; apply map_ext_in.
Qed.

Lemma app_prf [A B : Type] (f g : A -> B) (v1 v2 : A) :
  f = g -> v1 = v2 -> f v1 = g v2.
Proof. now intros fg v1v2; rewrite fg, v1v2. Qed.

Elpi Tactic replace.

Elpi Accumulate lp:{{

pred mk-app-prf i:list term, i:list term, i: list term, o:term.

mk-app-prf [F, _] [F, _] [{{@refl_equal _ _}}, P] {{f_equal lp:F lp:P}}.
mk-app-prf [F, _, _] [F, _, _] [{{@refl_equal _ _}}, P1, P2]
  {{f_equal2 lp:F lp:P1 lp:P2}}.
mk-app-prf [F, _, _, _] [F, _, _, _] [{{@refl_equal _ _}}, P1, P2, P3]
  {{f_equal3 lp:F lp:P1 lp:P2 lp:P3}}.
mk-app-prf [F, _, _, _, _] [F, _, _, _, _]
  [{{@refl_equal _ _}}, P1, P2, P3, P4]
  {{f_equal4 lp:F lp:P1 lp:P2 lp:P3 lp:P4}}.
% use nary_congruence from ssreflect
mk-app-prf [F, _, _, _, _, _] [F, _, _, _, _, _]
  [{{@refl_equal _ _}}, P1, P2, P3, P4, P5]
  {{f_equal5 lp:F lp:P1 lp:P2 lp:P3 lp:P4 lp:P5}}.

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

mk-equality (pr (trm S) (trm T)) S A T P A :- !,
  coq.typecheck P {{lp:S = lp:T}} ok,
  coq.say "rewrite happens".

:name "mk-equality:start"
mk-equality _RW X A Z Y A :- name X,!,
% coq.say "first clause",
X = Z, {{@refl_equal _ lp:X}} = Y, !.
mk-equality _RW (global _ as C) A C {{@refl_equal _ lp:C}} A :- !
% , coq.say "second clause" C
.
mk-equality _RW (pglobal _ _ as C) A C {{@refl_equal _ lp:C}} A :- !
% , coq.say "third clause"
.
mk-equality _RW (sort _ as C) A C {{@refl_equal _ lp:C}} A :- !
% , coq.say "fourth clause"
.

mk-equality RW (fun N T F as C) A C Res A :-
@pi-decl N T x\
  (instantiate_pair N T x RW (RW1 x),
   mk-equality (RW1 x) (F x) A _ {{@refl_equal _ _}} _A2,!,
   Res = {{@refl_equal _ _}},
   coq.say "fifth clause").

mk-equality RW (fun N T F) A (fun N T F1)
  {{functional_extensionality lp:{{(fun N T F)}} lp:{{(fun N T F1)}}
      lp:{{(fun N T Prf)}}}} A1 :- !,
      coq.say "sixth clause",
@pi-decl N T x\
  (std.assert! (instantiate_pair N T x RW (RW1 x)) "instantiate_pair failed",!,
   mk-equality (RW1 x) (F x) A (F1 x) (Prf x) A1).

% TODO: write unit tests for the following clauses
mk-equality RW (let N T B F as C) A C {{@refl_equal _ lp:C}} A :-
mk-equality RW B A _ {{@refl_equal _ _}} A2,
(@pi-decl N T x\
  (std.assert! (instantiate_pair N T x RW (RW1 x)) "instantiate_pair failed",!,
  mk-equality (RW1 x) (F x) A2 _ {{@refl_equal _ _}} _A3)),!,
  coq.say "seventh clause".

mk-equality RW (let N T B F) A (let N T B1 F1)
  {{let_congr lp:B lp:B1 lp:{{fun N T F}} lp:{{fun N T F1}}
      lp:PB lp:PF}} A3:- !,
mk-equality RW B A B1 PB A2,
@pi-decl N T x\
  (instantiate_pair N T x RW (RW1 x),!,
  coq.say "eigth clause",
   mk-equality (RW1 x) (F x) A2 (F1 x) PF A3).

mk-equality RW (prod N T F) A (prod N T F1) (fun N T P1) A2 :- !,
(@pi-decl N T x\
  (instantiate_pair N T x RW (RW1 x),!,
   mk-equality  (RW1 x) (F x) A (F1 x) (P1 x) A2)),!
   , coq.say "ninth clause"
.

mk-equality RW (app L as C) A C {{@refl_equal _ lp:C}} A :-
fold-map2 L A (mk-equality RW) _ L1 _A1,
std.forall L1 (c \ (sigma A B \ c = {{@refl_equal lp:A lp:B}})),!
, coq.say "tenth clause"
.

mk-equality RW {{@map lp:T1 lp:T2 lp:{{fun N _ F}} lp:L}}
  A
  {{@map lp:T1 lp:T2 lp:{{fun N T1 F1}} lp:L1}}
  R A2 :- !,
  % coq.say "eleventh clause",
  @pi-decl N T1 x\
  (instantiate_pair N T1 x RW (RW1 x),!,
    @pi-decl `H` (Ext_Hyp x) h\
      mk-equality (RW1 x) (F x) A (F1 x) (Pf x h) A1),
  mk-equality RW L A1 L1 Pl A2,
  R = {{map_ext_in_equal2 lp:{{fun N _ F}} lp:{{fun N _ F1}} lp:L lp:L1
         lp:{{fun N T1 x\
              (fun `H` (Ext_Hyp x) h\ Pf x h)}} lp:Pl }}.

mk-equality RW (app L) A (app L1) Prf A1 :-
L = [Hd | _], coq.term->string Hd S,
coq.say "entering twelfth" Hd S,
fold-map2 L A (mk-equality RW) L1 P1 A1,
if (non-dependent-type Hd, {std.length L} < 7)
  (mk-app-prf L L1 P1 Prf)
  (equal-app L L1 P1 Prf).

pred non-dependent-type  i:term.

non-dependent-type F :- coq.say "entered non-dependent-type" F, fail.

non-dependent-type F :-
  coq.typecheck F Ty ok,
  ndpt Ty.

pred ndpt i:term.

ndpt A :- coq.say "entered ndpt" A, fail.

ndpt (prod _N _T F) :-
  pi c1 c2\ F c1  = F c2,!,
  pi c\ ndpt (F c).

ndpt (prod _ _ _) :- !, fail.

ndpt _ :- !.


pred equal-app i:list term, i:list term, i:list term, o:term.

equal-app  [F, A] [F1, A1] [Pf, Pa]
  {{app_prf lp:F lp:F1 lp:A lp:A1 lp:Pf lp:Pa}} :- !.

equal-app [F, A | Args] [F1, A1 | Args1] [Pf, Pa | Ps]
    R :-
  equal-app [app [F, A] | Args] [app [F1, A1] | Args1]
    [{{app_prf lp:F lp:F1 lp:A lp:A1 lp:Pf lp:Pa}} | Ps] R.

mk-equality _RW (fix _N _Rno _Ty _F as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _RW (match _T _Rty _B as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _RW (primitive _ as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _RW (uvar _M _L as C) A C {{@refl_equal _ lp:C}} A :- !.
% when used in CHR rules
mk-equality _RW (uvar _X _L as C) A C {{@refl_equal _ lp:C}} A :- !.

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

solve (goal _ _ {{lp:_X = lp:Y }} _ [_, Arg1, Arg2] as G) GL :-
  coq.say "calling equality with " (pr Arg1 Arg2) Y,
  mk-equality (pr Arg1 Arg2) Y [] Y2 P _,
  coq.say "mk-equality succeeded" P,!,
  coq.term->string Y2 S,
  coq.term->string P SP,
  coq.say "prouf term" SP,
  std.assert-ok! (coq.typecheck P {{lp:Y = lp:Y2}}) "proof incorrect",
  coq.say "typecheck succeeded" S,!,
  refine {{@eq_trans _ _ lp:Y2 _ _ (eq_sym lp:P)}} G GL.
  % refine {{eq_sym (@eq_trans lp:Y lp:Y2 lp:X lp:P (eq_sym _))}} G GL.

solve (goal _ _ _ _ [Arg1, Arg2]) _ :-
  coq.say Arg1,
  coq.say Arg2,
  fail.

solve (goal _ _ _ _ [] as _G) _GL :-
  coq.say "failed".
}}.

Elpi Typecheck.

Tactic Notation (at level 0)  "replace_in_rhs" uconstr(A) uconstr(B) :=
 (elpi replace True A B;[lazy beta | ]).
(* this does not work because Ltac insists on have known unbound variables
  in arguments before passing them to other tactics.
 Ltac my_replace A B :=
 elpi replace True A B;[ lazy beta | ]. *)

Open Scope Z_scope.
Elpi Query lp:{{
  sigma T1 T2 A \
  {{fun x => x + (1 + 0)}} = T1,
  {{fun x => x + 1}} = T2,
  instantiate_pair `x` {{Z}} A (pr (open-trm 1 T1) (open-trm 1 T2)) R
}}.

(* With only two arguments, we use the variant corresponding to the
  first minimal working example, based on finding the left-most lambda,
  and then instantiating the unknown expression in the input terms with
  that lambda.  It only works if the expression-to-replace has exactly
  one-unknown and the other expression has at  most one unknown (assumed
  to be the same, without checking). )*)
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

(* With a third argument equal to True, the same tactic now uses an
  that proves only equalities. replacements only happen in the right-hand
  side, and both the expression-to-be-replaced and the replacing expression
  can have arbitrary many unknowns, which are filled with bound variables
  appearing in nested lambdas appearing in the term.  Replacement only
  happens when all unknowns have been filled. The goals are given in
  this order: first the equality between the expression-to-be-replace
  and the replacing expression in the context where the replacement occurs,
  second the goal after the replacement.  (TODO revese that order). *)

(* The first test illustrates the case where is no unknown. *)
Goal forall x, x = 1 -> 2 = x + 1.
intros x x1.
elpi replace True (x) (1);[ | assumption].
ring.
Qed.

(* The second test illustrates the case where there is one unknown in
  both the expression-to-be-replace and the replacing expression. *)
Goal forall l, map (fun x => x + 1) l = map (fun x => x + (1 + 0)) l.
Proof.
intros l.
elpi replace True (x + (1 + 0)) (x + 1).
  easy.
(* TODO: find how to have this goal beta-reduced. *)
lazy beta.
ring.
Qed.

Goal forall n, map (fun i => map (fun j => i + j) (map Z.of_nat (seq 1 n)))
  (map Z.of_nat (seq 1 n)) =
  map (fun i => map (fun j => j + i) (map Z.of_nat (seq 1 n)))
    (map Z.of_nat (seq 1 n)).
intros n.
elpi replace True (j + i) (i + j).
  easy.
(* TODO: find how to have this goal beta-reduced. *)
lazy beta.
ring.
Qed.

Goal forall l, fold_right Z.add 0 (map (fun x => x + 1) l) =
  fold_right Z.add 0 (map (fun x => 1 + x) l).
Proof.
intros l.
(* TODO : this should make some progress. *)
Fail progress elpi replace True (1 + x) (x + 1).
