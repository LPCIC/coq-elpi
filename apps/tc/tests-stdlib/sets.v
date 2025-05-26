From Coq Require Program.Tactics.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
From Coq Require Import ssreflect ssrbool ssrfun.
From elpi.apps Require Import tc coercion.

Set Printing All.
Elpi TC.Solver Override All.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

Set Default Timeout 1.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Local Open Scope set_scope.

(* Reasonable set of axioms for doing math. *)
Axiom propext : forall (P Q : Prop), (P <-> Q) -> P = Q.
Axiom PI : forall (P : Prop) (p q : P), q = p.
Axiom dfunext : forall A (B : A -> Type) 
  (f g : forall x, B x), (forall x, f x = g x) -> f = g.
Axiom CEM : forall (P : Prop), {P} + {~ P}.
Axiom CID : forall (T : Type) (P : T -> Prop), (exists x, P x) -> {x | P x}.
Arguments PI {P}.

Elpi Accumulate coercion.db lp:{{
solve (goal Ctx _ Ty Sol [trm V, trm VTy]) _ :- !,
  (@redflags! coq.redflags.all =>
    (coq.reduction.lazy.whd Ty Ty',
    coq.reduction.lazy.whd VTy VTy')),
  coercion Ctx V VTy' Ty' Sol.
}}.

Ltac done_tc := apply _.

(* Add typeclass resolution to trivial things
   (maybe dangerous in general, must be restricted). *)
Ltac done :=
  trivial; hnf; intros; (solve
   [ do
   ![ solve
    [ trivial | simple refine (eq_sym _); trivial ]
    | discriminate
    | contradiction
    | split ]
   | match goal with
     | H:~ _ |- _ => solve [ case H; trivial ]
     end
   | apply _ ]).

Reserved Notation "[ 'set' x : T | P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'set' x | P ]"
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]" (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' a ]"
  (at level 0, a at level 99, format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (at level 0, format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]"
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "[ 'set' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'set'  a1 ;  a2 ;  .. ;  an ]").
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `*`` B"  (at level 46, left associativity).
Reserved Notation "A ``*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (at level 1, left associativity, format "A .`1").
Reserved Notation "A .`2" (at level 1, left associativity, format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (at level 0, format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
(*
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
*)
Reserved Notation "\bigcup_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 1).
Reserved Notation "[ 'set`' p ]" (at level 0, format "[ 'set`'  p ]").
Reserved Notation "[ 'disjoint' A & B ]" (at level 0,
  format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'").
Reserved Notation "F `#` G"
 (at level 48, left associativity, format "F  `#`  G").
Reserved Notation "'`I_' n" (at level 8, n at level 2, format "'`I_' n").

(********************* Sets **************************)

(* TOTHINK: do I want to declare this through HB.structure? If yes, how do I
  get my current generic_set to be declared as canonical? *)
(* Design pattern for sets as subtypes. We use classes and structures instead
   of sig in order for the elaborator to instanciate holes in terms.*)
(* HB.mixin Record empty T (set_to_pred : T -> Prop) : Type := {}.
HB.structure Definition set (T : Type) := {
  set_to_pred of empty T set_to_pred
   }. *)
Structure set (T : Type) := MkSet {
  set_to_pred : T -> Prop
}.
Arguments set_to_pred : simpl never.

(* TOTHINK: unused for now. *)
(*Canonical generic_set T (P : T -> Prop) := MkSet P.*)

Class mem T (X : set T) (x : T)  := Mem { IsMem : set_to_pred X x }.

Notation "x \in X" := (@mem _ X x).
Notation "x \notin X" := (~ (x \in X)).

(* memType is the type of elements of a given set. *)
Module MemType.
Record type T (X : set T) := Pack { elt : T; memP : mem X elt }.
Definition pack T X elt eltP := @Pack T X elt eltP.
End MemType.
Notation memType := MemType.type.
Notation memP := MemType.memP.
Canonical MemType.pack.

Elpi Accumulate coercion.db lp:{{

coercion _ X _ {{ @MemType.type lp:E lp:S }} R :-
  coq.elaborate-skeleton X E Y ok,
  R = {{ @MemType.Pack lp:E lp:S lp:Y lp:C }},
  coq.typecheck C {{ @mem lp:E lp:S lp:Y }} ok,
  coq.ltac.collect-goals R [G] [], !,
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [].

coercion _ X {{ @MemType.type _ _ }} E R :-
  coq.elaborate-skeleton {{ (lp:X.(MemType.elt)) }} E R ok, !.
}}.

Check fun T (X : set T) (x : memType X) => x : T.

(* With this coercion, sets can be automatically used as types. *)
Coercion memType : set >-> Sortclass.

Check fun T (X : set T) (x : X) => x : T.
Check fun T (X : set T) (x : T) (h : x \in X) => x : X.

Lemma this_inj T (X : set T) : injective (id : X -> T).
Proof.
move=> [x +] [y yX]/= => /[swap] -> yX'.
do 3 f_equal.
exact: PI.
Qed.

Notation "x" := (@MemType.Pack _ _ x _) (at level 1, only printing).
Notation "x" := (@MemType.elt _ _ x) (at level 1, only printing).

(* With this coercion, sets can be automatically used as their predicate of
   membership (given by mem). *)
Definition set_to_pred_overlay (T : Type) (X : set T) := fun x => x \in X. 
Arguments set_to_pred_overlay /.
(*Coercion set_to_pred_overlay : set >-> Funclass.*)

Notation "[ 'set' x : T | P ]" := (@MkSet _ (fun x : T => P)) : set_scope.
Notation "[ 'set' x | P ]" := (@MkSet _ (fun x => P)) : set_scope.
Notation "[ 'set!' P ]" := (@MkSet _ P)
  (P at level 200, format "[ 'set!'  P ]") : set_scope.

Check fun (T : Type) (X : set T) (x : T) (xX : x \in X) => x : X.
Check fun (X : set nat) (x : X) (H : x \in [set n | n = 0]) => x : [set n | n = 0].

(* Obtaining the membership proof of (this V). *)
Elpi Accumulate TC.Solver lp:{{

% For (V : memType T X), we have (this V \in X) via memP.
% This rule should have priority over any other rule, so we put it before
% hook 0.
:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-mem T S {{ lp:X.(MemType.elt) }} R :-
  coq.typecheck X {{ @MemType.type lp:T lp:S }} ok,
  R = {{ lp:X.(MemType.memP) }}.

:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-mem T S X C :-
  coq.typecheck C {{ @mem lp:T lp:S lp:X }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "trivial") G [].

% :after "100"
% % Default rule, we try to brutally prove the membership property
% tc-elpi_apps_tc_tests_stdlib.sets.tc-mem T S X {{ @Mem lp:T lp:S lp:X lp:C }} :-
%   coq.typecheck C {{ @set_to_pred lp:T lp:S lp:X }} ok,
%   coq.ltac.collect-goals C [G] [],
%   coq.say "oops",
%   coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [],
%   coq.ltac.collect-goals C [] [].
% }}.

Check fun T (X : set T) (x : memType X) => _ : x \in X.

(* If a set X is defined directly using a predicate P, the membership 
  statement x \in X is equivalent to P x. *)
Lemma setE T (P : T -> Prop) x : x \in [set! P] = P x.
Proof. by apply/propext; split=> // -[]. Qed.

(* Extentionality of sets. *)
Lemma eq_set T (X Y : set T) : X = Y <-> (forall x, (x \in X) = (x \in Y)).
Proof.
split=> [->//|]; case: X Y => [P] [Q] /= eqXY.
by congr MkSet; apply/dfunext => x; have := eqXY x; rewrite !setE.
Qed.

(* TOTHINK : there was a `rewrite eq\_set` here, which does not work anymore
  for some reason. *)
Lemma eq_setP T (X Y : set T) : X = Y <-> (forall x, (x \in X) <-> (x \in Y)).
Proof.
by apply: (iff_trans (eq_set X Y)); split=> XY x;
  [rewrite XY//|apply/propext].
Qed.

(* If a set X is defined directly using a predicate P, an element of X
  satisfies P. *)
Lemma setP_def {T} {P : T -> Prop} (x : [set! P]) : P x.
Proof. by case: x => // ? []. Qed.

(* Why does `: set_scope` cause an error? *)
Notation setP X x := (setP_def (x : X)).
Notation "X .P x" := (setP X x) (format "X .P  x", at level 0) : set_scope.

Section basic_definitions.
Context {T U rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (g : T -> U -> rT) (Y : set rT).

Definition imset f (A : set T) :=
  [set y | exists x : A, f x = y].
Definition imset2 g (A : set T) (B : set U) :=
  [set z | exists (x : A) (y : B), g x y = z].
Definition preimage f Y : set T := [set t | f t \in Y].

Definition setT := [set _ : T | True].
Definition set0 := [set _ : T | False].
Definition set1 (t : T) := [set x : T | x = t].
Definition setI A B := [set x | x \in A /\ x \in B].
Definition setU A B := [set x | x \in A \/ x \in B].
Definition nonempty A := exists a, a \in A.
Definition setC A := [set a | ~ a \in A].
Definition setD A B := [set x | x \in A /\ ~ x \in B].
Definition setM T1 T2 (A1 : set T1) (A2 : set T2) := [set z | z.1 \in A1 /\ z.2 \in A2].
Definition fst_set T1 T2 (A : set (T1 * T2)) := [set x | exists y, (x, y) \in A].
Definition snd_set T1 T2 (A : set (T1 * T2)) := [set y | exists x, (x, y) \in A].
Definition setMR T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | z.1 \in A1 /\ z.2 \in A2 z.1].
Definition setML T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :=
  [set z | z.1 \in A1 z.2 /\ z.2 \in A2].

Definition bigcap T I (F : I -> set T) :=
  [set a | forall i, a \in F i].
Definition bigcup T I (F : I -> set T) :=
  [set a | exists i, a \in F i].

(* TOTHINK : or `forall t, t \in A -> t \in B` *)
Definition subset A B := forall (t : A), t \in B.
Local Notation "A `<=` B" := (subset A B).

Definition disj_set A B := setI A B = set0.

Definition proper A B := A `<=` B /\ ~ (B `<=` A).

End basic_definitions.

Coercion setT : Sortclass >-> set.

Notation "[ 'set' E | x 'in' A ]" :=
  (@imset _ _ (fun x => E) A) : set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  (@imset2 _ _ _ (fun x y => E) A B) : set_scope.
Notation "[ 'set' : T ]" := (@setT T) : set_scope.
Notation "[ 'set' a ]" := (set1 a) : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : set_scope.
Notation "A `|` B" := (setU A B) : set_scope.
Notation "a |` A" := ([set a] `|` A) : set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : set_scope.
Notation "A `&` B" := (setI A B) : set_scope.
Notation "~` A" := (setC A) : set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : set_scope.
Notation "A `\` B" := (setD A B) : set_scope.
Notation "A `\ a" := (A `\` [set a]) : set_scope.
Notation "A `*` B" := (setM A B) : set_scope.
Notation "A .`1" := (fst_set A) : set_scope.
Notation "A .`2" := (snd_set A) : set_scope.
Notation "A `*`` B" := (setMR A B) : set_scope.
Notation "A ``*` B" := (setML A B) : set_scope.

Notation "[ 'disjoint' A & B ]" := (disj_set A B) : set_scope.

(* TOTHINK : why is this not in set scope? *)
Notation "'`I_' n" := [set k | k < n].

(* The following two notations reduce to the same term since
   we have a coercion from set to Sortclass.*)
Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigcup (fun (i : P) => F)) : set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (bigcup (fun (i : T) => F)) : set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\bigcup_(i in `I_n) F) : set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap (fun (i : P) => F)) : set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (bigcap (fun (i : T) => F)) : set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\bigcap_(i in `I_n) F) : set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : set_scope.

Notation "A `<=` B" := (subset A B) : set_scope.
Notation "A `<` B" := (proper A B) : set_scope.

(* Should we have an extentionality lemma using this notation? *)
Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : set_scope.
Notation "f @` A" := (@imset _ _ f A) (only parsing) : set_scope.
Notation "f @^-1` A" := (preimage f A) : set_scope.
Notation "A !=set0" := (nonempty A) : set_scope.

Lemma set0fun {P T : Type} : @set0 T -> P. Proof. by case=> x; rewrite setE. Qed.

Section basic_membership.

Lemma mem_setT {T} (x : T) : x \in T. Proof. by []. Qed.

Elpi TC.Pending_lettify.
Elpi TC.AddInstances 1 mem_setT.

Check fun (x : nat) => x \in [set: nat].

Lemma mem_imset {T rT} (f : T -> rT) (A : set T) (x : A) : f x \in [set f x | x in A].
Proof. by rewrite setE; exists x. Qed.


Elpi Accumulate TC.AddInstances lp:{{
  % The goal is to programmatically generate the rules for the
  % schema: typechecking + collecting + solving if needed
  % This is done compiling the rule under an informative
  % attribute list carrying the info about which arguments have
  % to be used for typechecking
  func solve-proj-prem list int, list term, list term -> list prop. 
  solve-proj-prem [] _ [] [] :- !.
  solve-proj-prem [] _ L R :-
    R = [sigma Gs O\ 
         coq.ltac.collect-goals (app L) Gs O,
         msolve Gs []].
  solve-proj-prem [I1 | Ts] Args L [coq.typecheck K Ty ok|Xs] :-
    std.nth I1 Args K,
    decl K _ Ty,
    std.assert!(ground_term Ty) "The type is not ground...",
    solve-proj-prem Ts Args [K | L] Xs.

  namespace parse_int {
    func string->int string -> int.
    string->int S R :- R is string_to_int S.

    func parse-attr string -> list int.
    parse-attr S R :-
      rex.split "," S L,
      std.map L string->int R.

    func main -> list int.
    main R :-
      coq.parse-attributes {attributes} [att "pp" string] Opts,
      (Opts =!=> get-option "pp" Att), !,
      parse-attr Att R.
    main [].
  }

  :after "0"
  tc.compile.instance.compile-conclusion tt Goal Proof HOPremisesIn HOPremisesOut Premises Clause :- !,
    solve-proj-prem {parse_int.main} {coq.safe-dest-app Proof _} [] R,
    std.append {std.append HOPremisesIn Premises} {std.append HOPremisesOut R} AllPremises,
    tc.make-tc Goal Proof AllPremises tt Clause.
  :after "0"
  tc.compile.instance.compile-conclusion ff Goal Proof HOPremisesIn HOPremisesOut Premises Clause :- !,
    tc.make-tc Goal Proof Premises ff Clause1, 
    Clause = (do HOPremisesIn, Clause1, do HOPremisesOut).

}}.

(*
These 2 lines tell 
1. to lettify on the fly on the next term to compile
2. what arguments have to be taken to make typechecking (this is a WIP)
3. the addInstance
*)
Elpi TC.Pending_lettify.
#[pp="4"] Elpi TC.AddInstances 1 mem_imset.

Check fun (x : nat) => S x : [set S x | x in nat].

(*stop*)

Lemma mem_imset2 {T U rT} (f : T -> U -> rT) (A : set T) (B : set U) (x : A) (y : B) : f x y \in [set f x y | x in A & y in B].
Proof. by rewrite setE; exists x, y. Qed.

Elpi TC.Pending_lettify.
#[pp="6,7"] Elpi TC.AddInstances 1 mem_imset2.

Check fun (x : nat) => x + x : [set x + y | x in nat & y in nat].

Lemma mem_set1 {T} (x : T) : x \in [set x].
Proof. by exists. Qed.

Elpi TC.Pending_lettify.
Elpi TC.AddInstances 1 mem_set1.

(* Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver". *)

Check fun (x : nat) => x : [set x].

Lemma mem_setUl {T} (A B : set T) (x : A) : x \in A `|` B.
Proof. by rewrite setE; left. Qed.

Elpi TC.Pending_lettify.
#[pp="3"] Elpi TC.AddInstances 1 mem_setUl.
(* Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver". *)

Check fun (A : set nat) (x : A) => x : (A `|` (@set0 nat)).
Check fun (A : set nat) x => x : (x |` A).

Lemma mem_setUr {T} (A B : set T) (x : B) : x \in A `|` B.
Proof. by rewrite setE; right. Qed.

Elpi TC.Pending_lettify.
#[pp="3"] Elpi TC.AddInstances 1 mem_setUr.
(* Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver". *)


Check fun (A : set nat) (x : A) => x : ((@set0 nat) `|` A).
Check fun (A : set nat) (x : A) => x : (A `|` (@set0 nat)).

Lemma mem_setI {T} (A B : set T) (x : T) : x \in A -> x \in B -> x \in A `&` B.
Proof. by rewrite setE => xA xB; split. Qed.

Elpi TC.Pending_lettify.
Elpi TC.AddInstances 1 mem_setI.

Check fun (A B : set nat) (x : nat) (xA : x \in A) (xB : x \in B) => x : A `&` B.
Check fun (A B : set nat) (x : A) (xB : x \in B) => x : A `&` B.
Check fun (A B : set nat) (x : B) (xA : x \in A) => x : A `&` B.

Elpi Accumulate coercion.db lp:{{

coercion _ {{ @pair lp:A1 lp:A2 lp:X1 lp:X2 }}
           {{ @prod lp:A1 lp:A2 }}
           {{ @prod lp:B1 lp:B2 }} R :-
  coq.elaborate-skeleton {{ @pair lp:B1 lp:B2 lp:X1 lp:X2 }} {{ @prod lp:B1 lp:B2 }} R ok.

}}.

Lemma mem_setM {T1 T2} (A1 : set T1) (A2 : set T2) (x1 : A1) (x2 : A2) : (x1, x2) \in A1 `*` A2.
Proof. by rewrite setE/=; split. Qed.

Elpi TC.Pending_lettify.
#[pp="4,5"] Elpi TC.AddInstances 1 mem_setM.

Check fun T1 T2 (A1 : set T1) (A2 : set T2) (x1 : A1) (x2 : A2) => (x1, x2) : A1 `*` A2.

Lemma mem_fst {T1 T2} (A : set (T1 * T2)) (x : A) : x.1 \in A.`1.
Proof. by rewrite setE; exists x.2; rewrite -surjective_pairing. Qed.

Elpi TC.Pending_lettify.
#[pp="3"] Elpi TC.AddInstances 1 mem_fst.

Check fun T1 T2 (A : set (T1 * T2)) (x : A) => x.1 : A.`1.

Lemma mem_snd {T1 T2} (A : set (T1 * T2)) (x : A) : x.2 \in A.`2.
Proof. by rewrite setE; exists x.1; rewrite -surjective_pairing. Qed.

Elpi TC.Pending_lettify.
#[pp="3"] Elpi TC.AddInstances 1 mem_snd.

Check fun T1 T2 (A : set (T1 * T2)) (x : A) => x.2 : A.`2.

Lemma mem_setMR {T1 T2} (A1 : set T1) (A2 : T1 -> set T2) (x : A1) (y : A2 x) : (x, y) \in A1 `*`` A2.
Proof. by rewrite setE/=; split. Qed.

Elpi TC.Pending_lettify.
#[pp="4,5"] Elpi TC.AddInstances 1 mem_setMR.

Check fun T1 T2 (A1 : set T1) (A2 : T1 -> set T2) (x1 : A1) (x2 : A2 x1) => (x1, x2) : A1 `*`` A2.

Lemma mem_setML {T1 T2} (A1 : T2 -> set T1) (A2 : set T2) (y : A2) (x : A1 y) : (x, y) \in A1 ``*` A2.
Proof. by rewrite setE/=; split. Qed.

Elpi TC.Pending_lettify.
#[pp="4,5"] Elpi TC.AddInstances 1 mem_setML.

Check fun T1 T2 (A1 : T2 -> set T1) (A2 : set T2) (x2 : A2) (x1 : A1 x2) => (x1, x2) : A1 ``*` A2.

(* TOTHINK: The elaborator will not try to do this. *)
Lemma mem_bigcap {T I} (F : I -> set T) (x : T) : (forall i, x \in F i) -> x \in \bigcap_i F i.
Proof. by rewrite setE. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-mem T {{ @bigcap lp:T' lp:I lp:F }} X R :-
  coq.unify-eq T T' ok,
  (@pi-decl `i` I i\ tc-elpi_apps_tc_tests_stdlib.sets.tc-mem T {coq.mk-app F [i]} X (XF i)),
  R = {{ @mem_bigcap lp:T lp:I lp:F lp:X lp:{fun `i` I XF} }}.
}}.

Check fun T I (F : I -> set T) (x : T) (H : forall i, x \in F i) => x : \bigcap_i F i.

(* TOTHINK: Do I want to do bigcup? *)
End basic_membership.

(*
stop.

(********* Function restriction ****************)

(* TOTHINK : How about notations? *)
Check fun (T U : Type) (A : set T) (B : set U) (f : T -> U) (h : forall (x : A), f x \in B) => f : A -> B.

(************** Pointed Types ****************)

Class isPointed (T : Type) := Pointed {
  pt_subdef : T
}.

Module PointedType.
  Record type := Pack { sort : Type; sortP : isPointed sort }.
End PointedType.
Notation pointedType := PointedType.type.

Definition pt {T : pointedType} := @pt_subdef _ (PointedType.sortP T).

Coercion PointedType.sort : pointedType >-> Sortclass.

Elpi Accumulate coercion.db lp:{{

coercion _ X _ {{ PointedType.type }} R :-
  coq.elaborate-skeleton X {{ Type }} Y ok,
  coq.typecheck C {{ @isPointed lp:Y }} ok,
  coq.ltac.collect-goals C Gs [], !,
  std.forall Gs (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  R = {{ @PointedType.Pack lp:Y lp:C }}.

coercion _ X {{ PointedType.type }} E R :-
  coq.elaborate-skeleton {{ lp:X.(PointedType.sort) }} E R ok, !.
}}.

Elpi Accumulate TC.Solver lp:{{
:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-isPointed {{ lp:T.(PointedType.sort) }} {{ lp:T.(PointedType.sortP) }}.

:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-isPointed T C :-
  coq.typecheck C {{ @isPointed lp:T }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "trivial") G [].

:after "100"
% Default rule, we try to brutally prove the injectivity property
tc-elpi_apps_tc_tests_stdlib.sets.tc-isPointed T {{ @Pointed lp:T lp:C }} :-
  coq.typecheck C T ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [],
  coq.ltac.collect-goals C [] [].
}}.

(********* Function extension ****************)

(* Extending a function f from a subtype to the type, when the codomains are
  pointed types. When the input is in the domain of f, we apply f, otherwise
  we return the distinguished point of the codomain. *)
Definition extend (T : Type) (U : T -> pointedType) (A : set T)
  (f : forall a : A, U a) : forall a : T, U a :=
  fun x =>
  match CEM (x \in A) with
  | left xs => f x
  | right _ => pt
  end.

(* A function is automatically coercible to its extension, when applicable. *)
Elpi Accumulate coercion.db lp:{{

coercion _ V (prod _ TD TR) (prod _ ED ER) R :-
  coq.unify-eq TD {{ @memType lp:ED lp:X }} ok,
  (@pi-decl _ ED a\
    coq.unify-eq (ER a) {{ (lp:B lp:a).(PointedType.sort) }} ok,
    coq.unify-eq (TR a) {{ (lp:B (lp:a.(MemType.elt))).(PointedType.sort) }} ok),
  R = {{ @extend lp:ED lp:B lp:X lp:V }}.

}}.

Check fun (T : Type) (U : pointedType) (A : set T) (f : A -> U) => f : T -> U.

(* The support of a function with values in pointed types is the set of inputs
  whose images are not the distinguished point. *)
Definition support {A : Type} {B : A -> pointedType}
  (f : forall a : A, B a) : set A :=
  [set x | f x <> pt].

Goal forall (T : Type) (A : set T) (U : T -> pointedType)
  (f : forall a : A, U a), support (f : forall a : T, U a) `<=` A.
Proof.
move=> T A U f a.
move: (memP a).
rewrite setE /extend.
by case: (CEM _).
Qed.

(******* Additive types ********)

Class hasAdd T := HasAdd { add_op : T -> T -> T }.
#[global] Hint Mode hasAdd ! : typeclass_instances.

Module AddType.
  Record type := Pack { sort : Type; sortP : hasAdd sort }.
  Definition pack T (TP : hasAdd T) := Pack TP.
End AddType.
Notation addType := AddType.type.
Coercion AddType.sort : addType >-> Sortclass.
Canonical AddType.pack.

Notation "x" := (@AddType.Pack x _) (at level 1, only printing).
Notation "x" := (@AddType.pack x _) (at level 1, only printing).

Elpi Accumulate coercion.db lp:{{

coercion _ X _ {{ AddType.type }} R :-
  coq.elaborate-skeleton X {{ Type }} Y ok,
  coq.typecheck C {{ @hasAdd lp:Y }} ok,
  coq.ltac.collect-goals C Gs [],
  std.forall Gs (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  R = {{ @AddType.Pack lp:Y lp:C }}.

coercion _ X {{ AddType.type }} E R :-
  coq.elaborate-skeleton {{ lp:X.(AddType.sort) }} E R ok, !.
}}.

Elpi Accumulate TC.Solver lp:{{
:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAdd {{ lp:T.(AddType.sort) }} {{ lp:T.(AddType.sortP) }}.

:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAdd T C :-
  coq.typecheck C {{ @hasAdd lp:T }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "trivial") G [].

:after "100"
% Default rule, we try to brutally prove the injectivity property
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAdd T {{ @HasAdd lp:T lp:C }} :-
  coq.typecheck C {{ lp:T -> lp:T -> lp:T }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [],
  coq.ltac.collect-goals C [] [].
}}.

Definition add {T : addType} := (@add_op T _).
Notation "x +_ T y" := (@add T x y)
   (T at level 0, at level 60, only parsing).
Notation "x + y" := (@add _ x y).

Definition subAdd_axiom (T : addType) (dom : set T) :=
  forall a b, a \in dom -> b \in dom -> (a + b) \in dom.

Class isSubAdd (T : addType) (dom : set T) := IsSubAdd {
  isSubAddP : subAdd_axiom dom
}.
#[global] Hint Mode isSubAdd + ! : typeclass_instances.

Module AddSet.
  Record type (T : addType) := Pack { carrier : set T; carrierP : isSubAdd carrier }.
  Definition pack T C (CP : @isSubAdd T C) := Pack CP.
End AddSet.
Notation addSet := AddSet.type.
Coercion AddSet.carrier : addSet >-> set.
Canonical AddSet.pack.

Notation "x" := (@AddSet.Pack _ x _) (at level 1, only printing).
Notation "x" := (@AddSet.pack x _) (at level 1, only printing).

Elpi Accumulate coercion.db lp:{{

coercion _ X _ {{ @AddSet.type lp:T }} R :-
  coq.elaborate-skeleton X {{ @set (lp:T.(AddType.sort)) }} Y ok,
  R = {{ @AddSet.Pack lp:T lp:Y lp:C }},
  coq.typecheck C {{ @isSubAdd lp:T lp:Y }} ok,
  coq.ltac.collect-goals C [G] [], !,
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [].

coercion _ X {{ @AddSet.type _ }} E R :-
  coq.elaborate-skeleton {{ lp:X.(AddSet.carrier) }} E R ok, !.
}}.

Elpi Accumulate TC.Solver lp:{{
:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-isSubAdd _ {{ lp:X.(AddSet.carrier) }} {{ lp:X.(AddSet.carrierP) }}.
  %coq.unify-eq U {{ @AddType.Pack lp:T lp:Tadd }} ok.

:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-isSubAdd T X C :-
  coq.typecheck C {{ @isSubAdd lp:T lp:X }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "trivial") G [].

:after "100"
% Default rule, we try to brutally prove the injectivity property
tc-elpi_apps_tc_tests_stdlib.sets.tc-isSubAdd T X {{ @IsSubAdd lp:T lp:X lp:C }} :-
  coq.typecheck C {{ @subAdd_axiom lp:T lp:X }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [],
  coq.ltac.collect-goals C [] [].
}}.

(* FIXME: There are a few weird warnings here. *)
Lemma mem_add T (P : addSet T) (x : P) (y : P) : x +_T y \in P.
Proof. exact: isSubAddP. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-mem T P {{ @add lp:T' lp:X lp:Y }} R :-
  coq.unify-eq T {{ lp:T'.(AddType.sort) }} ok,
  coq.unify-eq P {{ lp:P'.(AddSet.carrier) }} ok,
  coq.unify-eq X {{ lp:X'.(MemType.elt) }} ok,
  coq.unify-eq Y {{ lp:Y'.(MemType.elt) }} ok,
  coq.typecheck T' {{ addType }} ok,
  coq.typecheck P' {{ @addSet lp:T' }} ok,
  coq.typecheck X' {{ @MemType.type lp:T lp:P }} ok,
  coq.typecheck Y' {{ @MemType.type lp:T lp:P }} ok,
  coq.ltac.collect-goals (app [T', P', X', Y']) Gs _,
  std.forall Gs (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  R = {{ @mem_add lp:T' lp:P' lp:X' lp:Y' }}.
}}.

Check fun T (P : addSet T) (x y : P) => x +_T y : P.

Definition addSet_hasAdd T (P : addSet T) : hasAdd P :=
  HasAdd (fun (x y : P) => x +_T y).

(* This one will be a problem for automation. How do I explain why I want to
  elaborate [P'] but not [T']? In other words, how do I say that the subject of
  the instance is morally [P] and not [@MemType.type T P]? *)
Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAdd {{ @MemType.type lp:T lp:P }} R :- 
  coq.unify-eq T {{ lp:T'.(AddType.sort) }} ok,
  coq.unify-eq P {{ lp:P'.(AddSet.carrier) }} ok,
  coq.typecheck T' {{ addType }} ok,
  coq.typecheck P' {{ @AddSet.type lp:T' }} ok,
  coq.ltac.collect-goals (app [T', P']) Gs _,
  std.forall Gs (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  R = {{ @addSet_hasAdd lp:T' lp:P' }}.
}}.

Check fun T (P : addSet T) => AddSet.carrier P : addType.

Lemma add_sub (T : addType) (P : addSet T) (x y : P) :
  x +_P y = x +_T y :> T.
Proof. by []. Qed.

Definition set_add (T : addType) : hasAdd (set T) :=
   HasAdd (fun X Y : set T => [set z | exists (x : X) (y : Y), z = x +_T y]).

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAdd {{ @set lp:T }} R :-
  coq.unify-eq T {{ lp:T'.(AddType.sort) }} ok,
  coq.typecheck T' {{ addType }} ok,
  coq.ltac.collect-goals T' Gs _,
  std.forall Gs (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  R = {{ @set_add lp:T' }}.
}}.

Check fun (T : addType) => set T : addType.

Record add_is_AC (T : addType) := AddIsAc
 { addA_subproof : associative (@add T);
   addC_subproof : commutative (@add T) }.

Class hasAcAdd (T : Type) := HasAcAdd
 {
  has_add_of_addac : hasAdd T;
  ac_of_addac : add_is_AC T
 }.

Coercion ac_of_addac : hasAcAdd >-> add_is_AC.

Module AcAddType.
  Record type := Pack { sort : Type; sortP : hasAcAdd sort }.
  Definition pack T (TP : hasAcAdd T) := Pack TP.
  Definition addType (T : type) := AddType.Pack (@has_add_of_addac _ (sortP T)).
End AcAddType.
Notation acAddType := AcAddType.type.
Coercion AcAddType.sort : acAddType >-> Sortclass.
Canonical AcAddType.pack.
Coercion AcAddType.addType : acAddType >-> addType.

Elpi Accumulate coercion.db lp:{{

coercion _ X _ {{ AcAddType.type }} R :-
  coq.elaborate-skeleton X {{ Type }} Y ok,
  coq.typecheck C {{ @hasAcAdd lp:Y }} ok,
  coq.ltac.collect-goals C [G] [], !,
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [],
  R = {{ @AcAddType.Pack lp:Y lp:C }}.

coercion _ X {{ AcAddType.type }} E R :-
  coq.elaborate-skeleton {{ lp:X.(AcAddType.sort) }} E R ok, !.
}}.

Elpi Accumulate TC.Solver lp:{{
:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAcAdd {{ lp:T.(AcAddType.sort) }} {{ lp:T.(AcAddType.sortP) }}.

:before "0"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAcAdd T C :-
  coq.typecheck C {{ @hasAcAdd lp:T }} ok,
  coq.ltac.collect-goals C [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "trivial") G [].

:after "100"
% Default rule, we try to brutally prove the injectivity property
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAcAdd T {{ @HasAcAdd lp:T lp:C lp:D }} :-
  coq.typecheck C {{ @hasAdd lp:T }} ok,
  coq.typecheck D {{ @add_is_AC (@AddType.Pack lp:T (@HasAdd lp:T lp:C)) }} ok,
  coq.ltac.collect-goals {{ @HasAcAdd lp:T lp:C lp:D }} [GC, GD] [],
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") GC [],
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") GD [].

:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAcAdd {{ lp:T.(AddType.sort) }} R :-
  (@redflags! coq.redflags.all => coq.reduction.lazy.whd T {{ @AddType.Pack lp:T' _ }}),
  tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAcAdd T' R.

}}.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-hasAdd {{ lp:T.(AcAddType.sort) }} {{ lp:T.(AcAddType.sortP).(has_add_of_addac) }}.
}}.

Check fun (T : acAddType) => T : addType.

Lemma addA (T : acAddType) : associative (@add T).
Proof. by apply: addA_subproof; apply: ac_of_addac. Qed.

Lemma addC (T : acAddType) : commutative (@add T).
Proof. by apply: addC_subproof; apply: ac_of_addac. Qed.

Lemma addAC (T : acAddType) : interchange (@add T) (@add T).
Proof.
move=> x y z t; rewrite !addA.
by congr (_ + _); rewrite -!addA; congr (_ + _); apply: addC.
Qed.

Lemma subadd_add (T : acAddType) (P Q : addSet T) : @isSubAdd T (P +_(set T) Q).
Proof.
split=> a b [[a1 [a2 ->]]] [[b1 [b2 ->]]].
by rewrite addAC; exists; exists (a1 + b1), (a2 + b2).
Qed.

Elpi Accumulate TC.Solver lp:{{

:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-isSubAdd T {{ @add lp:U lp:X lp:Y }} R :-
  coq.unify-eq {{ lp:T.(AddType.sort) }} {{ lp:T'.(AcAddType.sort) }} ok,
  coq.ltac.collect-goals T' GT _,
  std.forall GT (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  %When unifying structures, I should make sure that the structures are instantiated.
  coq.unify-eq {{ lp:U.(AddType.sortP) }} {{ @set_add (@AcAddType.addType lp:T') }} ok,
  coq.unify-eq X {{ lp:X'.(AddSet.carrier) }} ok,
  coq.unify-eq Y {{ lp:Y'.(AddSet.carrier) }} ok,
  coq.typecheck T' {{ acAddType }} ok,
  coq.typecheck X' {{ @AddSet.type (@AcAddType.addType lp:T') }} ok,
  coq.typecheck Y' {{ @AddSet.type (@AcAddType.addType lp:T') }} ok,
  coq.ltac.collect-goals (app [X', Y']) Gs _,
  std.forall Gs (g\ coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []),
  R = {{ @subadd_add lp:T' lp:X' lp:Y' }}.
}}.

Check fun (T : acAddType) (P Q : addSet T) => P +_(set (AcAddType.addType T)) Q : addSet (AcAddType.addType T).

(* We declare nat is an addType *)
(* The next 4 lines should be DSL directives *)
#[global] Instance nat_add : hasAdd nat := HasAdd plus.
#[global] Instance nat_acAdd : hasAcAdd nat.
Proof.
apply : HasAcAdd.
split; [exact: Nat.add_assoc | exact: Nat.add_comm].
Defined.

(* Even is a set, but it can be used as a type, see  *)
Definition even : set nat := [set n | exists m, n = 2 * m].
#[global] Typeclasses Opaque even.

(* We declare that even is additively stable and contains 0 *)
(* The next 12 lines should be DSL directives *)
Lemma even_subAdd : isSubAdd even.
Proof.
apply: IsSubAdd => a b aP bP.
have [m/= ->] := even.P a. have [n/= ->] := even.P b.
by exists; exists (m + n); rewrite /add/=; lia.
Qed.
(*#[global] Hint Extern 0 (isSubAdd _ _) =>
  apply: even_subAdd : typeclass_instances.
 *)

Elpi Accumulate TC.Solver lp:{{

:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-isSubAdd T {{ even }} {{ even_subAdd }} :-
  coq.unify-eq T {{ @AddType.Pack nat nat_add }} ok.

}}.

Lemma even0 : 0 \in even. Proof. by exists; exists 0. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-elpi_apps_tc_tests_stdlib.sets.tc-mem _ {{ even }} {{ 0 }} {{ even0 }}.
}}.

(* Types additifs *)
Check nat                 : addType.
Check set nat             : addType.
Eval cbn in (fun (X Y : set nat) => (X + Y)).
Check set (set nat)       : addType.

(* Parties stables par addition *)
Check even : addSet nat.
Check even + even : addSet nat.
Check (even + even : set nat) : addSet nat.

(* Elements d'un ensemble *)
Section tests.
Variables (n : nat) (n_even : n \in even) (m : even).

Check n : even.

Check n + m : nat.
Check n +_nat m.
Check m +_nat n.

Check m + n : even.
Check m +_even n.
Check n +_even m.

Check (n : even) + m.
Check (m : nat) + n.
Check (m : nat) + n : nat.

End tests.

Print even.
Lemma even2P (m n : even) : m +_nat n \in even + even.
Proof. by split; exists m, n. Qed.

Lemma add_even2 (m n : (even + even)%set) :
  m +_nat n \in even + even.
Proof. apply _. Qed.

(* Automatic inference makes proofs really easy *)
Lemma evenDeven_eq_even : even + even = even.
Proof.
apply/eq_setP => n; split.
  by move=> [[? [? ->]]].
by move=> n_even; split; exists 0, n.
Qed.

(* Coercions de fonctions *)
Check fun (A : Type) (B : Type)
  (S : set A) (S' : set B)
  (f : A -> B) (h : forall (x : S), f x \in S') =>
  (f : S -> S').

Check fun (A : Type) (B : pointedType) (S : set A)
  (f : S -> B) => f : A -> B.
*)