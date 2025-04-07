From elpi_stdlib Require Import ZArith Arith List FunctionalExtensionality.
From elpi Require Import elpi.

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

Lemma let_congr {T1 T2 : Type} (b1 b2 : T1) (F1 F2 : T1 -> T2) :
  b1 = b2 -> (forall x : T1, F1 x = F2 x) ->
  (let x := b1 in F1 x) = (let x := b2 in F2 x).
Proof.
intros bq fq; rewrite bq.
lazy zeta; apply fq.
Qed.

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
  (((pi N T F N1 T1 F1 \
    copy (fun N T F) (fun N1 T1 F1) :-
    copy T T1,
    fresh-name N T N1,
    (@pi-decl N1 T1 x\ 
      copy (F x) (F1 x))),
    (pi B B1 N T F N1 T1 F1 \
      copy (let N T B F)(let N1 T1 B1 F1) :-
        copy T T1,
        copy B B1,
        fresh-name N T N1,
        (@pi-decl N1 T1 x\ copy (F x) (F1 x))),
    (pi N T F N1 T1 F1 \
      copy (prod N T F) (prod N1 T1 F1) :-
        copy T T1,
        fresh-name N T N1,
        (@pi-decl N1 T1 x\
          copy (F x) (F1 x)))) => copy I O).

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

pred fold-map2 i:list term i:A i:(pred i:term, i:A, o:term, o:term, o:A)
  o:list term o:list term o:A.

fold-map2 [] A _ [] [] A.
fold-map2 [T | L] A F [T1 | L1] [P1 | PL] A2 :-
  F T A T1 P1 A1, fold-map2 L A1 F L1 PL A2.

pred instantiate_pair i:name, i:term, i:term, i:pair argument argument,
    o:pair argument argument.

pred instantiate i:name, i:term, i:term, i:argument, o:argument.

pred remove_one_unknown i:name, i:term, i:term, i:term, o:term.

% TODO : needs a fix in a rocq-elpi to detect if renaming has happened in
% in the current context.
remove_one_unknown N _T C (fun N1 _T1 F) Res :-
  {coq.name->id N} = {coq.name->id N1},!,
  Res = (F C),!.
 
 remove_one_unknown N T C (fun N1 T1 F) (fun N1 T1 Res) :-
  (@pi-decl N1 T1 x \
     remove_one_unknown N T C (F x) (Res x)),!.

instantiate N T C (open-trm 1 F) (open-trm 0 Res) :-
  remove_one_unknown N T C F Res,!.

instantiate N T C (open-trm I F) (open-trm J Res) :-
  remove_one_unknown N T C F Res,!,
  J is I - 1.

instantiate _N _T _C (open-trm 0 A) (open-trm 0 A):- !.

instantiate _N _T _C (open-trm _ _ as It) It :- !.

instantiate_pair N T C (pr A1 A2) (pr B1 B2) :-
  std.do! [
  std.assert! (instantiate N T C A1 B1) "first instantiate failed",
  instantiate N T C A2 B2].

pred mk-equality i:(pair argument argument), i:term i:A, o:term, o:term, o:A.

mk-equality (pr (open-trm 0 S) (open-trm 0 T)) S A T P A :- !,
  TY = {{lp:S = lp:T}},
  coq.typecheck-ty TY _ ok,
  coq.typecheck P TY ok.

:name "mk-equality:start"
mk-equality _RW X A Z Y A :- name X,!,
X = Z, {{@refl_equal _ lp:X}} = Y, !.

mk-equality _RW (global _ as C) A C {{@refl_equal _ lp:C}} A :- !.

mk-equality _RW (pglobal _ _ as C) A C {{@refl_equal _ lp:C}} A :- !.

mk-equality _RW (sort _ as C) A C {{@refl_equal _ lp:C}} A :- !.

mk-equality RW (fun N T F) A (fun N1 T F) Res A :-
fresh-name N T N1,
@pi-decl N T x\
  (instantiate_pair N T x RW (RW1 x),
   mk-equality (RW1 x) (F x) A _ {{@refl_equal _ _}} _A2,!,
   Res = {{@refl_equal _ _}}).

mk-equality RW (fun N T F) A (fun N1 T F1)
  {{functional_extensionality lp:{{(fun N T F)}} lp:{{(fun N T F1)}}
      lp:{{(fun N1 T Prf)}}}} A1 :- !,
fresh-name N T N1,
@pi-decl N1 T x\
  (std.assert! (instantiate_pair N1 T x RW (RW1 x)) "instantiate_pair failed",!,
   mk-equality (RW1 x) (F x) A (F1 x) (Prf x) A1).

% TODO: write unit tests for the following clauses
mk-equality RW (let N T B F as C) A (let N1 T B F) {{@refl_equal _ lp:C}} A :-
mk-equality RW B A _ {{@refl_equal _ _}} A2,
fresh-name N T N1,
(@pi-decl N1 T x\
  (std.assert! (instantiate_pair N1 T x RW (RW1 x)) "instantiate_pair failed",!,
  mk-equality (RW1 x) (F x) A2 _ {{@refl_equal _ _}} _A3)),!.

mk-equality RW (let N T B F) A (let N1 T B1 F1)
  {{let_congr lp:B lp:B1 lp:{{fun N1 T F}} lp:{{fun N1 T F1}}
      lp:PB lp:PF}} A3:- !,
fresh-name N T N1,
mk-equality RW B A B1 PB A2,
@pi-decl N1 T x\
  (instantiate_pair N1 T x RW (RW1 x),!,
   mk-equality (RW1 x) (F x) A2 (F1 x) PF A3).

mk-equality RW (prod N T F) A (prod N1 T F1) (fun N1 T P1) A2 :- !,
fresh-name N T N1,
(@pi-decl N1 T x\
  (instantiate_pair N1 T x RW (RW1 x),!,
   mk-equality  (RW1 x) (F x) A (F1 x) (P1 x) A2)),!.

mk-equality RW (app L as C) A C {{@refl_equal _ lp:C}} A :-
fold-map2 L A (mk-equality RW) _ L1 _A1,
std.forall L1 (c \ (sigma A B \ c = {{@refl_equal lp:A lp:B}})),!.

mk-equality RW {{@map lp:T1 lp:T2 lp:{{fun N _ F}} lp:L}}
  A
  {{@map lp:T1 lp:T2 lp:{{fun N1 T1 F1}} lp:L1}}
  R A2 :- !,
  fresh-name N T1 N1,
  @pi-decl N1 T1 x\
  (instantiate_pair N1 T1 x RW (RW1 x),!,
    @pi-decl `H` (Ext_Hyp x) h\
      mk-equality (RW1 x) (F x) A (F1 x) (Pf x h) A1),
  mk-equality RW L A1 L1 Pl A2,
  R = {{map_ext_in_equal2 lp:{{fun N1 _ F}} lp:{{fun N1 _ F1}} lp:L lp:L1
         lp:{{fun N1 T1 x\
              (fun `H` (Ext_Hyp x) h\ Pf x h)}} lp:Pl }}.

mk-equality RW (app L) A (app L1) Prf A1 :-
  fold-map2 L A (mk-equality RW) L1 P1 A1,
  mk-app-prf L L1 P1 Prf.

pred non-dependent-type  i:term.

non-dependent-type F :-
  coq.typecheck F Ty ok,
  ndpt Ty.

pred ndpt i:term.

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
  %coq.say Arg1 Arg2,
  mk-equality (pr Arg1 Arg2) Y [] Y2 P _,
  std.assert-ok! (coq.typecheck P {{lp:Y = lp:Y2}}) "proof incorrect",!,
  preserve_bound_variables X X1,
  refine {{@eq_trans _ lp:X1 lp:Y2 _ _ (eq_sym lp:P)}} G GL,
  if (GL = [Ng, Ng2])
    (coq.ltac.open (coq.ltac.call "lazy_beta" []) Ng2 GL_aux,
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

Tactic Notation (at level 0) "repl" uconstr(x) uconstr(y) :=
  (elpi replace ltac_open_term:(x) ltac_open_term:(y)).

Open Scope Z_scope. (* Otherwise ring fails. *)

(* The tactic repl only handles goals that have the shape of an
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
repl x 1;[ | assumption].
ring.
Qed.

(* This test illustrates the case where there is one unknown in
  both the expression-to-be-replaced and the replacing expression. *)
Goal forall l, map (fun x => x + 1) l = map (fun x => x + (1 + 0)) l.
Proof.
intros l.
repl (x + (1 + 0)) (x + 1); cycle 1.
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
repl (j + i) (i + j).
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
repl (x - x) 0; cycle 1.
  ring.
symmetry.
apply (fold_neutral Z.add 0 Z.add_0_r).
Qed.

(* This test illustrates the case where the formula to be replaced contains
  no instance of a bound variable, but the replacing formula does. *)
Goal forall (l : list Z), 0 = fold_right Z.add 0 (map (fun x => x - x + 0) l).
intros l.
repl 0 (x - x); cycle 1.
  ring.
repl (x - x + (x - x)) 0; cycle 1.
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
repl (x0 + (y + 0)) (x0 + y).
progress repl (x0 + y) (y + x0).
repl (y + x0) (x0 + y).
easy.
all:ring.
Qed.

(* If there are several lambda expressions, one of which is not concerned
  with the rewrite rule, it should not fail. *)

Goal forall l, l = map (fun x => x + 1) (map (fun y => y - 1) l).
Proof.
intros l.
repl(x + 1) (1 + x); cycle 1.
  ring.
repl (y - 1) ((-1) + y); cycle 1.
  ring.
rewrite map_map.
repl (1 + ((-1) + x)) x; cycle 1.
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
repl (x0 + (y + 0)) (x0 + y); cycle 1.
  ring.
(* TODO: elpi generates an ugly name in a subterm of the goal that we did not
  modify, when it could avoid it. *)
now apply map_ext_in; intros a _; ring.
Qed.

End sandbox.

