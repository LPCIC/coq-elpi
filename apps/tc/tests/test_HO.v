From elpi Require Import tc.

Set TC NameShortPath.

(* Module FO_app.

  Class nice_predicate {T : Type} (P : T -> Prop).

  Instance partial_app: forall (T : Type) (P : T -> T -> Prop), forall x, nice_predicate (P x). Qed.

    Elpi Print TC.Solver.
  Elpi Accumulate TC.Solver lp:{{

  % Since (P X) would be too HO for elpi (not pattern fragment), we use the FO approximation
  %tc-nice_predicate T (app L) {{ @partial_app lp:T lp:P lp:X }} :-
  %  unify-FO L 1 P [X].

  % Since (P x) has type (prod _ _ _) we also want to support eta for the class
  % tc-nice_predicate T (fun _ _ _ as F) S :-
  %   coq.reduction.eta-contract F G, not (F == G), tc-nice_predicate T G S.

  }}.
  Elpi Typecheck TC.Solver.

  Elpi Print TC.Solver.
  Elpi Trace Browser.
  Lemma ex1 (T : Type) (p : nat -> T -> T -> Prop) (x : T) : nice_predicate (p 0 x).
    apply _.
  Defined.
  Check eq_refl : ex1 = fun T p x => @partial_app T (p 0) x.

  Lemma ex2 (T : Type) (p : nat -> T -> T -> Prop) y : nice_predicate (fun x => p 0 y x).
    apply _.
  Defined.
  Check eq_refl : ex2 = fun T p y => @partial_app T (p 0) y.

  Existing Instance partial_app.
  Elpi Override TC TC.Solver None.


  Lemma ex3 (T : Type) (p : nat -> T -> T -> Prop) y : nice_predicate (fun x => p 0 x y).
    Fail apply _. (* Coq KO *)
    Fail apply partial_app. (* Coq KO *)
    apply (@partial_app T (fun a b => p 0 b a) y).
  Abort.

  Lemma ex4 (T : Type) (p : nat -> T -> T -> Prop) y : nice_predicate (fun x => p 0 y x).
    Fail apply _. (* Coq KO *)
    Succeed apply partial_app. (* Coq eta! *)
    apply (@partial_app T (p 0) y).
  Abort.

End FO_app.

Elpi Override TC TC.Solver All.

Module FO_app1.

  Class Singleton (B: Type).
  Class Singleton1 (B: Type).

  Instance s M: (forall A : Type, Singleton1 (M A)) -> forall A : Type, Singleton (M A). Qed.

  Goal forall M, (forall A : Type, Singleton1 (M A)) -> forall A : Type, Singleton (M A).
  apply _.
  Qed.

End FO_app1.

Module FO_app2.

  Context (A B : Type).

  Class Functional (B: Type).

  Instance s1 F: Functional (F B) -> Functional (F B) -> Functional (F A). Qed.

  Elpi Print TC.Solver.

  Definition F (x : Type) := Type.
  Context (H : Functional (F B)).

  Goal Functional (F A).
    apply _.
  Abort.

End FO_app2.

(************************************************************************)

Module HO_PF.

  Class Extensionality (T : Type).

  Instance fun_1 (A1 : Type) (A2 : A1 -> Type) : Extensionality (forall a : A1, A2 a). Qed.

  Elpi Accumulate TC.Solver lp:{{

  % Since app[A2, a] is in the pattern fragment we rephrase it
  % as (A2_PF a) and A2 = {{ fun x => lp:(A2_PF x) }} and then
  % eta contract
  %tc-Extensionality (prod _ A1 a\ A2_PF a) {{ @fun_1 lp:A1 lp:A2 }} :-
  %  coq.reduction.eta-contract {{ fun a : lp:A1 => lp:(A2_PF a) }} A2.

  % this simple version would work for odd, but not for the x = x + 1 example.
  % in the lucky case of odd, we would not need the eta contraction
  % tc-Extensionality (prod _ A1 a\ app [A2, a]) {{ @fun_1 lp:A1 lp:A2 }}.
  % this is the version which is easy to explain but in the odd case
  % generates an ugly expansion
  % tc-Extensionality (prod _ A1 a\ A2_PF a) {{ @fun_1 lp:A1 lp:A2 }} :-
  %  A2 = {{ fun a : lp:A1 => lp:(A2_PF a) }}.

  }}.
  Elpi Typecheck TC.Solver.

  Lemma ex1 : Extensionality (nat -> nat). apply _. Defined.
  Check eq_refl : ex1 = @fun_1 nat (fun _ => nat).

  Lemma ex2 : Extensionality (forall x : nat, x = x + 1). apply _. Defined.
  Check eq_refl : ex2 = @fun_1 nat (fun a => a = a + 1).

  Axiom odd : nat -> Type.

  Lemma ex3 : Extensionality (forall x : nat, odd x). apply _. Defined.
  Goal ex3 = ex3. unfold ex3. match goal with |- @fun_1 nat odd = _ => idtac end. reflexivity. Abort.

  (* Instance for multiple lambdas *)
  Instance fun_2 (A1 : Type) (A2 : A1 -> A1 -> Type) : Extensionality (forall a b : A1, A2 b a). Qed.
  Lemma ex4 : Extensionality (nat -> nat -> nat). apply _. Qed. 

End HO_PF.  *)


Module HO_PF1.
  Parameter A : Type.
  Class Decision (P : Type).
  (* Global Hint Mode Decision ! : typeclass_instances. *)

  Class Exists (P : A -> Type) (l : A).
  Instance Exists_dec (P : A -> Type): (forall x, Decision (P x)) -> forall l, Decision (Exists P l). Qed.
  Elpi Print TC.Solver.

  (* tc-Decision (app [global (indt «Exists»), A8, A0]) 
 (app [global (const «Exists_dec»), A8, A3, A0]) :-
 [ho-link A8 (prod `_` (global (const «A»)) c0 \ sort (typ A9)) A7, 
  ho-link A3 
   (prod `x` (global (const «A»)) c0 \
     app [global (indt «Decision»), app [ho-var A8 0, c0]]) A2, 
  pi c0 \
   decl c0 `x` (global (const «A»)) =>
    do
     [tc-Decision (A5 c0) (A2 c0), 
      ho-link A8 (prod `_` (global (const «A»)) c1 \ sort (typ A9)) A5, 
      ho-link A3 
       (prod `x` (global (const «A»)) c1 \
         app [global (indt «Decision»), app [ho-var A8 0, c1]]) A2]]. *)

(* 
∀ P : A → Type, (∀ x : A, Decision (P x)) → ∀ l : A, Decision (Exists P l)

  P is used twice: A6 -> [A5, A7] for HO unification
    We have to link A6 with them before anithing is done, otherwise we risk
    to make recursive calls on too much generic variable and create loops.

  The hyp H, has functional type and is a class: A3

*)

(* 
  FUNZIONA
  tc-Decision (app [global (indt «Exists»), A6, A0]) 
 (app [global (const «Exists_dec»), A6, A3, A0]) :-
 [ho-link A6 (prod `_` (global (const «A»)) c0 \ sort (typ A7)) A5, 
  pi c0 \
   decl c0 `x` (global (const «A»)) =>
    do
     [tc-Decision (A5 c0) (A2 c0), 
      ho-link A3 
       (prod `x` (global (const «A»)) c1 \
         app [global (indt «Decision»), app [A6, c1]]) A2, 
      ho-link A6 (prod `_` (global (const «A»)) c1 \ sort (typ A7)) A5]].




tc-Decision (app [global (indt «Exists»), A8, A0]) 
 (app [global (const «Exists_dec»), A8, A3, A0]) :-
 [ho-link A8 (prod `_` (global (const «A»)) c0 \ sort (typ A9)) A7, 
  pi c0 \
   decl c0 `x` (global (const «A»)) =>
    do
     [ho-link A8 (prod `_` (global (const «A»)) c1 \ sort (typ A9)) A5, 
      tc-Decision (A5 c0) (A2 c0), 
      ho-link A3 
       (prod `x` (global (const «A»)) c1 \
         app [global (indt «Decision»), app [ho-var A8 0, c1]]) A2], 
  ho-link A3 
   (prod `x` (global (const «A»)) c0 \
     app [global (indt «Decision»), app [ho-var A8 0, c0]]) A2].

*)
 (* TUTTI LINK 
 
 tc-Decision (app [global (indt «Exists»), A8, A0]) 
 (app [global (const «Exists_dec»), A8, A3, A0]) :-
 [ho-link A8 (prod `_` (global (const «A»)) c0 \ sort (typ A9)) A7, 
  ho-link A3 
   (prod `x` (global (const «A»)) c0 \
     app [global (indt «Decision»), app [ho-var A8 0, c0]]) A2, 
  
  ho-link A8 (prod `_` (global (const «A»)) c0 \ sort (typ A9)) A5, 
  ho-link A8 (prod `_` (global (const «A»)) c0 \ sort (typ A9)) A7, 
  ho-link A3 
   (prod `x` (global (const «A»)) c0 \
     app [global (indt «Decision»), app [ho-var A8 0, c0]]) A2, 
  
  pi c0 \
   decl c0 `x` (global (const «A»)) =>
    do
     [tc-Decision (A5 c0) (A2 c0), 
      ho-link A8 (prod `_` (global (const «A»)) c1 \ sort (typ A9)) A5, 
      ho-link A3 
       (prod `x` (global (const «A»)) c1 \
         app [global (indt «Decision»), app [ho-var A8 0, c1]]) A2]].
 *)


(* Senza tutti link
tc-Decision (app [global (indt «Exists»), A8, A0]) 
 (app [global (const «Exists_dec»), A8, A3, A0]) :-
 [ho-link A8 (prod `_` (global (const «A»)) c0 \ sort (typ A9)) A7, 
  ho-link A3 
   (prod `x` (global (const «A»)) c0 \
     app [global (indt «Decision»), app [ho-var A8 0, c0]]) A2, 
  pi c0 \
   decl c0 `x` (global (const «A»)) =>
    do
     [tc-Decision (A5 c0) (A2 c0), 
      ho-link A8 (prod `_` (global (const «A»)) c1 \ sort (typ A9)) A5, 
      ho-link A3 
       (prod `x` (global (const «A»)) c1 \
         app [global (indt «Decision»), app [ho-var A8 0, c1]]) A2]].


tc-Decision (app [global (indt «Exists»), c1, c9]) 
 (app [global (const «Exists_dec»), c1, c6, c9]) :-
 [ho-link c1 (prod `_` (global (const «A»)) c10 \ sort (typ c0)) c2, 
  /* ho-link c1 (prod `_` (global (const «A»)) c10 \ sort (typ c0)) c4,  */
  ho-link c6 
   (prod `x` (global (const «A»)) c10 \
     app [global (indt «Decision»), app [ho-var c1 0, c10]]) c7, 
  pi c10 \
   decl c10 `x` (global (const «A»)) =>
    do
     [tc-Decision (c4 c10) (c7 c10), 
      ho-link c1 (prod `_` (global (const «A»)) c11 \ sort (typ c0)) c4, 
      ho-link c6 
       (prod `x` (global (const «A»)) c11 \
         app [global (indt «Decision»), app [ho-var c1 0, c11]]) c7]]

 *)


  Elpi Print TC.Solver.

  Section test.

    Goal forall P (l:A) , Decision (Exists P l).
    Proof.
      intros. 
      Fail apply _. (* We fail without infinite loop thanks to ho-links *)
    Abort.

  End test.


 Lemma ho_in_elpi (P1: A -> Prop) l:
    exists (P : A -> A -> A -> Prop), forall z y , (forall x, Decision (P1 x)) 
      -> Decision (Exists (P z y) l) /\ P z y y = P1 z.
  Proof.
    eexists; intros.
    split.
    (* We take the most general solution for P, it picks P = (fun a b c => P1 ?x) *)
    apply _.
    simpl.
    (* Reflexivity fix ?x = a hence (fun a b c => P1 a) z y y = P1 z is solvable *)
    reflexivity.
  Qed.
xxx.
 Lemma ho_in_coq (P1: A -> Prop) l:
    exists (P : A -> A -> A -> Prop), forall z y , (forall x, Decision (P1 x)) 
      -> Decision (Exists (P z y) l) /\ P z y y = P1 z.
  Proof.
    Elpi Override TC TC.Solver None.
    eexists; intros.
    split.
    (* Coq doesn't give the most general solution for P, it picks P = (fun _ _ x => P1 x) *)
    apply _.
    simpl.
    Fail reflexivity.
  Abort.

  Section test.

    Axiom (P1: Type -> Prop).
    Context (H : Decision (P1 nat)).
    Goal exists P, forall (x y:A) , Decision (P x y).
    Proof.
      eexists; intros.
      Set Printing Existential Instances.
      apply _.
    Abort.

  End test.

End HO_PF1.

Section HO_PF2.
  Class cl1 (i : Type).
  Class cl2 {i : Type} (y : cl1 i).
  Class cl3 {i : Type} (y : cl1 i).
  Instance i1 : 
    forall (H : forall x, cl1 x), 
    cl2 (H nat) -> cl3 (H bool). Qed.
  Elpi Print TC.Solver.

  Goal forall (H : forall x, cl1 x), 
    cl2 (H nat) -> cl3 (H bool).
  Proof.
    apply _.
  Qed.

  Goal forall (H : forall x, cl1 x), 
    cl2 (H nat) -> exists x (i_cl1: cl1 x), cl3 i_cl1.
  Proof.
    intros.
    do 2 eexists.
    apply _.
  Qed.
End HO_PF2.

