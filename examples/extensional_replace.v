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

Lemma app_prf1 [A : Type] [B : A -> Type] (f g : forall x, B x) (v : A) :
  f = g -> f v = g v.
Proof. now intros fg; rewrite fg. Qed.

Ltac lazy_beta := lazy beta.

Elpi Tactic replace.

Elpi Accumulate lp:{{

pred preserve_bound_variables i:term o:term.

preserve_bound_variables I O :-
  ((pi N T F N1 T1 F1 \
    copy (fun N T F) (fun N1 T1 F1) :-
    copy T T1,
    fresh-name N T N1,
    (@pi-decl N1 T1 x\ 
      copy (F x) (F1 x))) => copy I O).

pred fresh-name i:name, i:term, o:name.

fresh-name N T M :-
  coq.ltac.fresh-id {coq.name->id N} T Mi,
  coq.id->name Mi M.

pred mk-app-prf i:list term, i:list term, i: list term, o:term.

mk-app-prf [F, _] [F, _] [{{@refl_equal _ _}}, P] {{f_equal lp:F lp:P}} :-
  non-dependent-type F,!.
mk-app-prf [F, _, _] [F, _, _] [{{@refl_equal _ _}}, P1, P2]
  {{f_equal2 lp:F lp:P1 lp:P2}} :-
  non-dependent-type F,!.
mk-app-prf [F, _, _, _] [F, _, _, _] [{{@refl_equal _ _}}, P1, P2, P3]
  {{f_equal3 lp:F lp:P1 lp:P2 lp:P3}} :-
  non-dependent-type F,!.
mk-app-prf [F, _, _, _, _] [F, _, _, _, _]
  [{{@refl_equal _ _}}, P1, P2, P3, P4]
  {{f_equal4 lp:F lp:P1 lp:P2 lp:P3 lp:P4}} :-
  non-dependent-type F,!.
% TODO use nary_congruence from ssreflect
mk-app-prf [F, _, _, _, _, _] [F, _, _, _, _, _]
  [{{@refl_equal _ _}}, P1, P2, P3, P4, P5]
  {{f_equal5 lp:F lp:P1 lp:P2 lp:P3 lp:P4 lp:P5}} :-
  non-dependent-type F,!.
mk-app-prf [F1, A] [F2, A] [Pf, {{@refl_equal _ _}}]
   {{app_prf1 lp:F1 lp:F2 lp:A lp:Pf}} :- !.
mk-app-prf [F1, A] [F2, B] [Pf, Pa]
  {{app_prf lp:F1 lp:F2 lp:A lp:B lp:Pf lp:Pa}} :-
  coq.typecheck F1 (prod _ _ Ft) ok,
  (pi c1 c2 \ Ft c1 = Ft c2),!.
 mk-app-prf [F1, A | Args1] [F2, A |Args2] [Pf, {{@refl_equal _ _}} | Ps]
   P :- !,
    mk-app-prf [app [F1, A] | Args1] [app [F2, A] | Args2]
      [{{app_prf1 lp:F1 lp:F2 lp:A lp:Pf}} | Ps] P.

mk-app-prf [F1, A | Args1] [F2, B | Args2] [Pf, Pa | Ps] P :-
  coq.typecheck F1 (prod _ _ Ft) ok,
  (pi c1 c2 \ Ft c1 = Ft c2),!,
  mk-app-prf [app [F1, A] | Args1] [app [F2, B] | Args2]
    [{{app_prf lp:F1 lp:F2 lp:A lp:B lp:Pf lp:Pa}} | Ps] P.

pred fold-map2 i:list term i:A i:(term -> A -> term -> term -> A -> prop)
  o:list term o:list term o:A.

fold-map2 [] A _ [] [] A.
fold-map2 [T | L] A F [T1 | L1] [P1 | PL] A2 :-
  F T A T1 P1 A1, fold-map2 L A1 F L1 PL A2.

pred instantiate_pair i:name, i:term, i:term, i:pair argument argument,
    o:pair argument argument.

pred instantiate i:name, i:term, i:term, i:argument, o:argument.

pred remove_one_unknown i:name, i:term, i:term, i:term, o:term.

% TODO : needs a fix in a coq-elpi to detect if renaming has happened in
% in the current context.
remove_one_unknown N _T C (fun N1 _T1 F) Res :-
  {coq.name->id N} = {coq.name->id N1},!,
  Res = (F C),!,
   coq.say "remove the unknown" Res.

% remove_one_unknown N T C (fun N1 _T1 F) Res :-
%   {coq.ltac.fresh-id {coq.name->id N} T} = {coq.name->id N1},!,
%   Res = (F C),!,
%    coq.say "remove the unknown 2" Res.

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

instantiate _N _T _C (open-trm _ _ as It) It :- !.

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

mk-equality RW (fun N T F) A (fun N1 T F) Res A :-
fresh-name N T N1,
@pi-decl N T x\
  (instantiate_pair N T x RW (RW1 x),
   mk-equality (RW1 x) (F x) A _ {{@refl_equal _ _}} _A2,!,
   Res = {{@refl_equal _ _}},
   coq.say "fifth clause").

mk-equality RW (fun N T F) A (fun N1 T F1)
  {{functional_extensionality lp:{{(fun N T F)}} lp:{{(fun N T F1)}}
      lp:{{(fun N1 T Prf)}}}} A1 :- !,
coq.say "sixth clause",
fresh-name N T N1,
@pi-decl N1 T x\
  (std.assert! (instantiate_pair N1 T x RW (RW1 x)) "instantiate_pair failed",!,
   mk-equality (RW1 x) (F x) A (F1 x) (Prf x) A1).

% TODO: write unit tests for the following clauses
mk-equality RW (let N T B F as C) A (let N1 T B F) {{@refl_equal _ lp:C}} A :-
mk-equality RW B A _ {{@refl_equal _ _}} A2,
fresh-name N T N1,
coq.say "old name - new name" N N1,
(@pi-decl N1 T x\
  (std.assert! (instantiate_pair N1 T x RW (RW1 x)) "instantiate_pair failed",!,
  mk-equality (RW1 x) (F x) A2 _ {{@refl_equal _ _}} _A3)),!,
  coq.say "seventh clause".

mk-equality RW (let N T B F) A (let N1 T B1 F1)
  {{let_congr lp:B lp:B1 lp:{{fun N1 T F}} lp:{{fun N1 T F1}}
      lp:PB lp:PF}} A3:- !,
fresh-name N T N1,
mk-equality RW B A B1 PB A2,
@pi-decl N1 T x\
  (instantiate_pair N1 T x RW (RW1 x),!,
  coq.say "eigth clause",
   mk-equality (RW1 x) (F x) A2 (F1 x) PF A3).

mk-equality RW (prod N T F) A (prod N1 T F1) (fun N1 T P1) A2 :- !,
fresh-name N T N1,
(@pi-decl N1 T x\
  (instantiate_pair N1 T x RW (RW1 x),!,
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
  {{@map lp:T1 lp:T2 lp:{{fun N1 T1 F1}} lp:L1}}
  R A2 :- !,
  fresh-name N T1 N1,
  % coq.say "eleventh clause",
  @pi-decl N1 T1 x\
  (instantiate_pair N1 T1 x RW (RW1 x),!,
    @pi-decl `H` (Ext_Hyp x) h\
      mk-equality (RW1 x) (F x) A (F1 x) (Pf x h) A1),
  mk-equality RW L A1 L1 Pl A2,
  R = {{map_ext_in_equal2 lp:{{fun N1 _ F}} lp:{{fun N1 _ F1}} lp:L lp:L1
         lp:{{fun N1 T1 x\
              (fun `H` (Ext_Hyp x) h\ Pf x h)}} lp:Pl }}.

mk-equality RW (app L) A (app L1) Prf A1 :-
  L = [Hd | _], coq.term->string Hd S,
  coq.say "entering twelfth" Hd S,
  fold-map2 L A (mk-equality RW) L1 P1 A1,
  mk-app-prf L L1 P1 Prf.

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

solve (goal _ _ {{lp:X = lp:Y }} _ [Arg1, Arg2] as G) GL1 :-
  coq.say "calling equality with " (pr Arg1 Arg2) Y,
  mk-equality (pr Arg1 Arg2) Y [] Y2 P _,
  coq.say "mk-equality succeeded" P,!,
  coq.term->string Y2 S,
  coq.term->string P SP,
  coq.say "prouf term" SP,
  std.assert-ok! (coq.typecheck P {{lp:Y = lp:Y2}}) "proof incorrect",
  coq.say "typecheck succeeded" S,!,
  preserve_bound_variables X X1,
  refine {{@eq_trans _ lp:X1 lp:Y2 _ _ (eq_sym lp:P)}} G GL,
  if (GL = [Ng, Ng2])
    (coq.say "two subgoals",
     coq.ltac.open (coq.ltac.call "lazy_beta" []) Ng2 GL_aux,
     GL1 = [Ng | GL_aux])
    (GL1 = GL).
  % refine {{eq_sym (@eq_trans lp:Y lp:Y2 lp:X lp:P (eq_sym _))}} G GL.

solve (goal _ _ _ _ [Arg1, Arg2]) _ :-
  coq.say Arg1,
  coq.say Arg2,
  fail.

solve (goal _ _ _ _ [] as _G) _GL :-
  coq.say "failed".
}}.

Elpi Typecheck.

Open Scope Z_scope. (* Otherwise ring fails. *)

(* The tactic elpi replace only handles goals that have the shape of an
  equality, and only attempts to perform rewrites in the right-hand-side of
  that equality. In this example, we replace a formula containing a variable
  that is not well defined outside the map expression with a formula that also
  contains the such a variable.  But a variable with the same name is
  actually bound in the goal, and the expression to be replaced occurs inside
  the lambda-expression.
  The number of variables occuring in the replacement formulas that
  are unknown at the root of the goals conclusion can be arbitrary big,
  but they all have to be fillable with bound variables where the binding
  happens in the goal, in a nested fashion. *)

(* This test illustrates the case where there is no unknown. *)
Goal forall x, x = 1 -> 2 = x + 1.
intros x x1.
elpi replace (x) (1);[ | assumption].
ring.
Qed.

(* This test illustrates the case where there is one unknown in
  both the expression-to-be-replaced and the replacing expression. *)
Goal forall l, map (fun x => x + 1) l = map (fun x => x + (1 + 0)) l.
Proof.
intros l.
elpi replace (x + (1 + 0)) (x + 1); cycle 1.
  ring.
easy.
Qed.

(* This test illustrates the case where there are two unknowns in
  both the expression-to-be-replaced and the replacing expression. *)
Goal forall n,
  map (fun i => map (fun j => (i + j)) (map Z.of_nat (seq 1 n)))
  (map Z.of_nat (seq 1 n)) =
  map (fun i => map (fun j => (j + i)) (map Z.of_nat (seq 1 n)))
    (map Z.of_nat (seq 1 n)).
intros n.
elpi replace (j + i) (i + j).
  easy.
ring.
Qed.

(* This is a typical bigop theorem. The proof does not use our new
  tactic. *)
Lemma fold_neutral {A B : Type}(f : A -> A -> A) (a0 : A) :
  (forall x, f x a0 = x) ->
  forall (l : list B), fold_right f a0 (map (fun x => a0) l) = a0.
Proof.
intros neutral; induction l as [ | b l Ih]; simpl; try rewrite Ih; auto.
Qed.

(* The next two tests illustrate the fact that the whole formula may contain
  polymorphic functions. *)
(* This test illustrates the case where the formula to be replaced contains
  an instance of the variable bound in a lambda expression occuring in the
  right-hand-side of the equality, but the replacing formula does not. *)
Goal forall l, fold_right Z.add 0 (map (fun x => x - x) l) = 0.
Proof.
intros l.
symmetry.
(* TODO: this should not fail. *)
elpi replace (x - x) (0); cycle 1.
  ring.
symmetry.
apply (fold_neutral Z.add 0 Z.add_0_r).
Qed.

(* This test illustrates the case where the formula to be replaced contains
  no instance of a bound variable, but the replacing formula does. *)
Goal forall (l : list Z), 0 = fold_right Z.add 0 (map (fun x => x - x + 0) l).
intros l.
elpi replace (0) (x - x); cycle 1.
  ring.
elpi replace (x - x + (x - x)) (0); cycle 1.
  ring.
symmetry.
apply fold_neutral.
intros x; ring.
Qed.

(* this illustrates the case where a bound variable is clashing with another
  existing variable in the context, with the same name. *)
Goal forall (x : Z) l y, map (fun x => x + y) l = map (fun x => x + (y + 0)) l.
Proof.
intros x l y.
(* This illustrates that the names seen by the user are recognized properly
  by the tactic.*)
elpi replace (x0 + (y + 0)) (x0 + y).
progress elpi replace (x0 + y) (y + x0).
elpi replace (y + x0) (x0 + y).
easy.
all:ring.
Qed.

(* If there are several lambda expressions, one of which is not concerned
  with the rewrite rule, it should not fail. *)

Goal forall l, l = map (fun x => x + 1) (map (fun y => y - 1) l).
Proof.
intros l.
elpi replace(x + 1) (1 + x); cycle 1.
  ring.
elpi replace (y - 1) ((-1) + y); cycle 1.
  ring.
rewrite map_map.
elpi replace (1 + ((-1) + x)) (x); cycle 1.
  ring.
rewrite map_id.
easy.
Qed.

Section sandbox.

Variable x : Z.

(* This goal illustrates the case where a bound variable clashes with
  a section variable. *)
Goal forall l y, map (fun x => x + y) l = map (fun x => x + (y + 0)) l.
Proof.
intros l y.
elpi replace (x0 + (y + 0)) (x0 + y); cycle 1.
  ring.
(* TODO: elpi generates an ugly name in a subterm of the goal that we did not
  modify, when it could avoid it. *)
now apply map_ext_in; intros a _; ring.
Qed.

End sandbox.