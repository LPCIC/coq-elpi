From elpi Require Import elpi.
Require Import Arith ZArith List FunctionalExtensionality.

Axiom map2 : (nat -> nat -> nat) -> list nat -> list nat -> list nat.

(* This example make use of the open-trm argument type in order to
   implement a tactic that takes in input expressions mentioning
   variables that are bound in the goal (and not in the proof context) *)

Lemma easy_example : forall x, x + 1 = 1 + x.
Proof.
  intros x.
  (* easy: x is bound by the proof context *)
  replace (x + 1) with (1 + x) by ring.
  reflexivity.
Qed.

Lemma hard_example : forall l, map (fun x => x + 1) l = map (fun x => 1 + x) l.
Proof.
  intros l.
  (* hard: x is bound by a lambda in the goal *)
  Fail replace (x + 1) with (1 + x) by ring.
  (* fails and prints: The variable x was not found in the current environment.*)

  (* This example implements a new repl tactic that will instead succeed. *)
Abort.

(* Elpi provides a type of tactic argument called open-trm for terms
    with free variables. Since there is no such a thing as free variables
    in Elpi, a pre-processor closes the term under binders and pairs the
    closed term with the number of such "technical binders". *)

Elpi Tactic show_open_term.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [open-trm N F]) _ :-
    coq.say "The argument " {coq.term->string F} "was closed under" N "binders".
}}.

Goal map (fun x => x + x) nil = nil :> list nat.
elpi show_open_term `(x + _).
(* prints: The argument fun x : ?e => x + ?e1 was closed under 1 binders *)
Abort.

(* A key step in the implementation of repl is to align the technical binders
   of the open term with actual binders present in the goal. For this
   we use the names as written by the user. We call this operation instantiate *)

(* We put the code into a file, so that we can reuse it later *)
Elpi File instantiate.code lp:{{

% [instantiate-replacement N Ty x L R L1 R1] is called when crossing
% a goal binder for the variable x named N and of type Ty. The replacement
% L with R  is instantiated (if possible) to  L1 with R1
pred instantiate-replacement i:name, i:term, i:term, i:argument, i:argument, o:argument, o:argument.
instantiate-replacement N Ty C L R L1 R1 :- std.do! [
  instantiate N Ty C L L1,
  instantiate N Ty C R R1,
].

pred instantiate i:name, i:term, i:term, i:argument, o:argument.
instantiate _ _ _ (open-trm 0 A) (open-trm 0 A) :- !.
instantiate N T C (open-trm I F) (open-trm J F1) :- remove-binder-for N T C F F1, !,
  J is I - 1.
instantiate _ _ _ X X.

pred remove-binder-for i:name, i:term, i:term, i:term, o:term.
% we found the binder
remove-binder-for N _ C (fun N1 _ F) Res :- {coq.name->id N} = {coq.name->id N1}, !,
  % Remember that in Elpi all names are the same, eg `x` = `y`
  % coq.name->id gives a string, the string used for printing, and as one expects
  % not("x" = "y")
  Res = (F C).
% we cross the binder and look deeper
remove-binder-for N T C (fun N1 T1 F) (fun N1 T1 F1) :-
  @pi-decl N1 T1 x \ remove-binder-for N T C (F x) (F1 x).

}}.


Elpi Tactic test_instantiate.
Elpi Accumulate File instantiate.code.
Elpi Accumulate lp:{{
solve (goal _ _ {{ map2 lp:F _ _ = _ }} _ [(open-trm _ LF as L), (open-trm _ RF as R)]) _ :-
  coq.say "old replacement:" {coq.term->string LF} "with" {coq.term->string RF},
  F = fun N Ty _,
  @pi-decl N Ty x\
    instantiate-replacement N Ty x L R (open-trm _ (L1 x)) (open-trm _ (R1 x)),
    coq.say "new replacement:" {coq.term->string (L1 x)} "with" {coq.term->string (R1 x)}.

}}.


Goal map2 (fun x y => x - y) nil nil = nil.
elpi test_instantiate `(x - y) `(y + x).
(* prints: 
old replacement:
  fun (x : ?e) (y : ?e0) => x - y
with
  fun (y : ?e1) (x : ?e2) => y + x

new replacement:
  fun y : ?e0 => x - y
with
  fun y : ?e1 => y + x

Remark that the technical binders are generated following a left-to-right
traversal of the term, hence their order varies. This is the reason why we
need the second rule for remove-binder-for.

Also remark that L1 and R1 need to see the variable we crossed, and that
is bound by pi: we are capturing the free variable by it (or better removing
the techincal binding and replacing that bound variable by the variable bound
by pi).

*)
Abort.


(* We need a few helpers to cross the context *)

Lemma congrP (A : Type) (B : A -> Type) (f g : forall x : A, B x) :
  f = g -> forall v1 v2 (p : v1 = v2), match p in _ = x return B x with eq_refl => f v1 end = g v2.
Proof. now intros fg v1 v2 v1v2; rewrite fg, v1v2. Qed.

Lemma congrA (A B : Type) (f g : A -> B) :
  f = g -> forall v1 v2 (p : v1 = v2), f v1 = g v2.
Proof. now intros fg v1 v2 v1v2; rewrite fg, v1v2. Qed.

Elpi File congruence.code lp:{{

% iterates congrA and congrP to prove f x1..xn = f y1..yn from proofs of xi = yi
% [congruence F G PFG Ty XS YS PXYS R] starting from a proof PFG that F = G
% it consumes X Y and PXY : X = Y to build a proof R : (F X = G Y). It needs to
% look at the type of F (and G) in order to decide which congruence lemma to apply
pred conguence i:term, i:term,  i:term, i:term, i:list term, i:list term, i: list term, o:term.
conguence _ _ P _ [] [] [] P :- !.
conguence F G PFG {{ _ -> lp:Ty }} [X|XS] [Y|YS] [PXY|PS] Q :- !,
  PFXGY = {{ congrA _ _ lp:F lp:G lp:PFG lp:X lp:Y lp:PXY }},
  conguence {coq.mk-app F [X]} {coq.mk-app G [Y]} PFXGY Ty XS YS PS Q.
conguence F G PFG {{ forall x, lp:(Ty x) }} [X|XS] [Y|YS] [PXY|PS] Q :-
  PFXGY = {{ congrP _ _ lp:F lp:G lp:PFG lp:X lp:Y lp:PXY }},
  conguence {coq.mk-app F [X]} {coq.mk-app G [Y]} PFXGY (Ty X) XS YS PS Q.

}}.

Elpi Tactic test_congruence.
Elpi Accumulate File congruence.code.
Elpi Accumulate lp:{{
  pred mk-refl i:term, o:term.
  mk-refl T {{ @refl_equal Type lp:T }} :- coq.typecheck-ty T _ ok, !. % we don't like Set
  mk-refl T {{ refl_equal lp:T }}.

  solve (goal _ _ {{ lp:A = lp:B }} _ _ as G) GL :- std.do! [
    A = app[HD|Args1],
    B = app[HD|Args2],
    std.map2 Args1 Args2 (_\ mk-refl) Proofs,
    coq.typecheck HD Ty ok,
    conguence HD HD {{ refl_equal lp:HD }} Ty Args1 Args2 Proofs P,
    refine P G GL,
].
}}.

Goal forall l, map (fun x => x) l = map (fun x => x) l :> list nat.
intros.
elpi test_congruence.
Qed.

(* We now build the final tactic *)

Elpi Tactic replace.
Elpi Accumulate File instantiate.code.
Elpi Accumulate File congruence.code.
Elpi Accumulate lp:{{


% [replace L R X Y P] replaces L by R in X obtaining Y and
% a proof P that X = Y. P will contain holes (sub goals) for sub proofs
% of L = R.
pred replace i:argument, i:argument, i:term, o:term, o:term.

% all binders are crossed and we find a term identical to L.
% the proof is a hole of type L = R.
replace (open-trm 0 L) (open-trm 0 R) L R P :- !,
  TY = {{ lp:L = lp:R }},
  coq.typecheck-ty TY _ ok,
  coq.typecheck P TY ok.

% we cross the binder by functional extensionality
replace L R (fun N T F) (fun N T F1) {{ functional_extensionality lp:{{ fun N T F }} lp:{{ fun N T F1 }} lp:{{ fun N T Prf }}}} :- !,
  @pi-decl N T x\
    instantiate-replacement N T x L R (L1 x) (R1 x),
    replace (L1 x) (R1 x) (F x) (F1 x) (Prf x).

replace L R (app [HD|TS]) (app [HD|TS1]) Prf :-
  replace-list L R TS TS1 PS,
  coq.typecheck HD Ty ok,
  conguence HD HD {{ refl_equal lp:HD }} Ty TS TS1 PS Prf.

% base cases
replace _ _ X X {{ refl_equal lp:X }} :- name X, !.
replace _ _ (global _ as C) C {{ @refl_equal Type lp:C }} :- coq.typecheck-ty C _ ok, !. % we don't like Set
replace _ _ (global _ as C) C {{ refl_equal lp:C }} :- !.
% we omit rules for primitive constants, fixpoints, let, forall, ...

pred replace-list i:argument, i:argument, i:list term, o:list term, o:list term.
replace-list _ _ [] [] [].
replace-list L R [X|XS] [Y|YS] [P|PS] :- replace L R X Y P, replace-list L R XS YS PS.

solve (goal _ _ {{ lp:X = lp:Y }} _ [(open-trm _ _ as L), (open-trm _ _ as R)] as G) GL :- !, std.do! [
  replace L R X X1 P,
  refine {{ @eq_trans _ lp:X lp:X1 lp:Y lp:P _ }} G GL,
].

solve (goal _ _ {{ _ = _ }} _ _) _ :- !, coq.error "elpi: replace: the goal is not an equality".
solve _ _ :- !, coq.error "elpi: replace: the two arguments must be open terms".

}}.

Tactic Notation (at level 0) "repl" uconstr(x) "with" uconstr(y) :=
  elpi replace ltac_open_term:(x) ltac_open_term:(y); simpl.

Tactic Notation (at level 0) "repl" uconstr(x) "with" uconstr(y) "by" tactic(t) :=
  elpi replace ltac_open_term:(x) ltac_open_term:(y); try (simpl; t).

Lemma hard_example : forall l, map (fun x => x + 1) l = map (fun x => 1 + x) l.
Proof.
  intros l.
  repl (x + 1) with (1 + x) by ring.
  reflexivity.
Qed.

Lemma hard_example2 : forall l, map2 (fun x y => x + 0 + y) l l = map2 (fun x y => y + x) l l.
Proof.
  intros l.
  repl (x + 0 + y) with (y + x) by ring.
  reflexivity.
Qed.

(* An extended version of this tactic by Y. Bertot can be found in the tests/
   directory under the name test_open_terms.v *)
