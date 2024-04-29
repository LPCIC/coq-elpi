From elpi Require Import tc.

Set TC NameShortPath.

Module FO_prod.
  Context (A B : Type) (y : B) (Q : A -> Prop).
  
  Class Ccc (i : Prop).
  Global Instance i P : Ccc (forall (x: A), P x y). Qed.

  Elpi Accumulate TC.Solver lp:{{
  % tc-Ccc (prod `x` ({{A}}) c0 \ app (A0 c0)) 
  %   (app [{{i}}, A2]) :-
  %   pi c0 \
  %     do
  %     [unify-FO (A0 c0) 2 A2 [c0, {{y}}], 
  %       ho-link A2
  %         (prod `x` ({{A}}) c1 \ prod `x0` ({{B}}) c2 \ sort prop) A1_]
  }}. 
  Elpi Typecheck TC.Solver.
  Goal forall (P : nat -> A -> B -> Prop), Ccc (forall x, P 0 x y).
    apply _.
  Qed.
End FO_prod.


Module FO_app.

  Class nice_predicate {T : Type} (P : T -> Prop).

  Instance partial_app: forall (T : Type) (P : T -> T -> Prop), forall x, nice_predicate (P x). Qed.

  (* 
    Unification is done between `p 0 x` and `P X` (The latter is not in PF)
    The former's elpi representation is `app [p, {{0}}, x]` while the latter is `P t p x (X t p x)` 
      - `t` stands for T : Type
      - `P` is the unif variable `P` in partial_app
      - `X` is the unif variable `x` in partial_app
    We are outside the pattern fragment.
    The heuristics splits the arguments of `P` into `[t, p, x]` and `[(X t p x)]`, 
      where `[t,p,x]` is the longest prefix in PF and `(X t p x)` is the remaining
      tail. We call the former PF and the latter NPF
    Len N the length of NPF and M the length of `[p, {{0}}, x]`, 
    then we split `[p, {{0}}, x]` at position `M - N`. We obtain the sublists:
    `[p, {{0}}]` and `[x]`. We then unify `[x]` with `[(X t p x)]`.
    Let `L` the concatenation of `PF` and `NPF`, then the head P of the elpi unification 
    variable is obtained by adding 4 lambda abstraction (the length of `L`), 
    and for each abstraction `x` at depth `i` we add the local clause `copy L.(i) x`.
    The final result is `P = (x\y\z\w\ app[y, {{0}}, w])`
  *)
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
    Unshelve.
    apply nat.
  Qed.

End FO_app1.

Module FO_app2.

  Context (A B : Type).

  Class Functional (B: Type).

  Instance s1 F: Functional (F B) -> Functional (F B) -> Functional (F A). Qed.


  Definition f (x : Type) := Type.
  Context (H : Functional (f B)).

  Goal Functional (f A).
    apply _.
  Abort.

End FO_app2.

Module FO_app3.
  Definition X := Type -> Type.
  Axiom f : X.
  Class C (I : Type -> Type).

  Instance I : C (fun _ => f nat). Qed.

  Goal exists (R : Type -> Type) , forall (T:Type), C (fun x => R T) /\ R bool = f nat.
    eexists.
    intros.
    split.
    (* Here we commit the only existing solution for R, that is, 
       R := fun _ => f nat,
       note that R does not see T *)
    apply _.
    reflexivity.
  Qed.

  Goal exists (R : Type -> Type) , C (fun x => R nat) /\ R bool = f nat.
    eexists.
    split.
    (* Here we do not commit the mgu. There are two solutions for R 
      1. R := fun _ => f nat
      2. R := fun x => f x == f,
      in our case we commit the second *)
    apply _.
    Show Proof.
    Fail reflexivity.
    (* ============= We restart and try the good sol ============= *)
    Restart.
    exists (fun x => f nat).
    split.
    apply _.
    reflexivity.
  Qed.

  Goal exists (R : Type -> Type) , C (fun x => R unit) /\ R bool = f nat.
    eexists.
    (* Here we fail, even though there exists the solution R := fun _ => f nat *)
    Fail apply _.
    Unshelve.
    2:{ refine (fun x => f nat). }
    split.
    apply _.
    reflexivity.
  Qed.

  Goal exists (R : Type -> Type) , C (fun x => R nat) /\ R bool = f bool.
    eexists.
    split.
    apply _.
    reflexivity.
  Qed.
End FO_app3.

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

End HO_PF. 


Module HO_PF1.
  Parameter A : Type.
  Class Decision (P : Type).
  (* Global Hint Mode Decision ! : typeclass_instances. *)

  Class Exists (P : A -> Type) (l : A).
  Instance Exists_dec (P : A -> Type): (forall x, Decision (P x)) -> forall l, Decision (Exists P l). Qed.

   Section test.

    Goal forall P (l:A) , Decision (Exists P l).
    Proof.
      intros. 
      Fail apply _. (* We fail without infinite loop thanks to ho-links *)
    Abort.

  End test. 


  (* TODO:  *)
  (*Lemma ho_in_elpi (P1: A -> Prop) l:
    exists (P : A -> A -> A -> Prop), forall z y , (forall x, Decision (P1 x)) 
      -> Decision (Exists (P z y) l) /\ P z y y = P1 z.
  Proof.
    eexists; intros.
    split.
    Elpi Trace Browser.
    Set Printing Existential Instances.
    (* forall x : A, Decision (P1 x) = forall x : A, Decision ((?P z y) x) *)
    (* x |- Decision (P1 ?x) =  Decision ((?P z y) x) *)
    (* We take the most general solution for P, it picks P = (fun a b c => P1 ?x) *)
    apply _.
    simpl.
    (* Reflexivity fix ?x = a hence (fun a b c => P1 a) z y y = P1 z is solvable *)
    reflexivity.
  Qed. *)

   Lemma ho_in_coq (P1: A -> Prop) l:
    exists (P : A -> A -> A -> Prop), forall z y , (forall x, Decision (P1 x)) 
      -> Decision (Exists (P z y) l) /\ P z y y = P1 z.
  Proof.
    Elpi Override TC TC.Solver None.
    eexists; intros.
    epose (H _).
    clearbody d.
    clear H.
    split.
    (* Print HintDb typeclass_instances. *)
    (* Set Elpi Typeclasses Debug. *)
    (* Coq doesn't give the most general solution for P, it picks P = (fun _ _ x => P1 x) *)
    Fail Timeout 1 apply _.
    simpl.
  Abort.
Elpi Override TC TC.Solver All.

  Section test.

    Context (P1: Type -> Prop).
    Context (H : Decision (P1 nat)).
    Goal exists P, forall (x y:A) , Decision (P x y).
    Proof.
      eexists; intros.
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

Module D.

  Class C1 (T : Type -> Type) (i: forall x, T x).

  Class D.
  Instance I : forall (T : Type -> Type) (H : forall x, T x), 
    C1 T (fun x => H x) -> D . Qed. 
  
  Instance J: forall (T : Type -> Type) (H : forall x, T x), C1 T H. Qed.
  
  Goal D.
    intros.
    apply _.
    Unshelve.
    apply nat.
    apply 3.
  Qed.

End D.


Module F.

  Class C1 (T : Type -> Type) (i: forall x, T x).

  Class D.
  Instance I : forall (T : Type -> Type) (H : forall x, T x), 
    C1 T (fun x => H x) -> D . Qed. 
  
  Goal forall (T : Type -> Type) (H : forall x, T x), C1 T H -> D.
    intros.
    apply _. (* qui coq non ce la fa. Se l'istanza ha una eta-expand (fun x -> f x), 
                coq non la unifica con la forma base f*)
  Qed.

End F.

Module F'.

  Class C2 (T : Type -> Type) (i: forall x, T x).

  Class D.
  Instance I : forall (T : Type -> Type) (H : forall x, T x), 
    C2 T H -> D . Qed. 
  
  Goal forall (T : Type -> Type) (H : forall x, T x), C2 T (fun x => H x) -> D.
    intros.
    apply _. (* qui al contrario ce la fa, nel goal la eta viene ridotta per poi
                unificare con I*)
  Qed.

End F'.

Module E.
  Class C3 (i : nat -> nat -> nat).
  Instance I : C3 (plus). Qed.

  Class D3 (i : Prop).
  
  Instance I2 (F : nat -> nat -> nat) : C3 F -> D3 (forall x y, F x y = F y x) . Qed.
  Goal D3 (forall n m, n + m = m + n).
    apply _.
  Qed.
End E.
