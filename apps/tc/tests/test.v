From elpi Require Import tc.

Module simpleHO.
  Class A (t : nat -> nat) (t' : Type).
  Class B (t : nat) (t' : Type).

  Instance I1: forall F c, (forall a, B (F a) c) -> A F c. Qed.
  Instance I2 : B 3 bool. Qed.
  Goal exists x, A x bool.
  Proof. 
    eexists.
    apply _.
  Qed.
End simpleHO.

Module HO_1.
  Axiom (f : bool -> unit -> nat -> nat).
  
  Class A (t : bool -> unit -> nat -> nat).
  Class B (t : unit -> nat -> nat).
  Class C (t : nat).

  Instance I1: forall a b, (C (f true a b)). Qed.
  Instance I2: forall F, (forall x y, C (F x y)) -> B F. Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal B (fun x y => f true x y).
    apply _.
  Qed.

  Goal exists x, A x.
    eexists.
    Time apply _.
    Unshelve.
    (* Note: here we find a most general solution than Coq's one *)
    apply tt.
    apply 3.
  Qed.

End HO_1.

Module HO_2.
  Axiom f : Type -> Type -> Type.

  Class A (t : Type -> Type -> Type) (t : Type -> Type -> Type).

  Instance I: forall f, A f (fun x y => f y x). Qed.
  
  Goal A f (fun x y => f y x).
    apply _.
  Qed.
End HO_2.

Module HO_3.
  Axiom (f : nat -> nat -> nat).

  Class A (t : nat -> nat -> nat -> nat).
  Class B (t : nat -> nat -> nat).
  Class C (t : nat -> nat).

  Instance I1: (C (f 3)). Qed.
  Instance I2: forall F, (forall x, C (F x)) -> B F. Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal exists x,B x.
    eexists.
    apply _.
  Qed.
End HO_3.


Module HO_4.
  Axiom (f : nat -> nat -> nat -> nat).

  Class A (t : nat -> nat -> nat -> nat -> nat -> nat).
  Class B (t : nat -> nat -> nat -> nat -> nat).
  Class C (t : nat -> nat -> nat).

  Instance I1: C (fun x => f x 3). Qed.
  Instance I2: forall F, (forall x y, C (F x y)) -> B (fun a b => F b a). Qed.
  Instance I3: forall F, (forall x, B (F x)) -> A F. Qed.

  Goal exists x, A x.
    eexists.
    apply _.
  Qed.
End HO_4.


Module HO_swap.
  Axiom (f : Type -> Type -> Type).
  Elpi Query TC.Solver lp:{{
    tc.link.maybe-eta (fun `x` _ c0 \ fun `y` _ c1 \ A2 c1 c0),
    tc.link.maybe-eta (fun `x` _ c0 \ fun `y` _ c1 \ A2 (A c1) c0),
    tc.link.maybe-eta {{fun x y => f x y}}.
  }}.

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).

  Elpi Query TC.Solver lp:{{
    @pi-decl `x` {{Type -> Type}} f\ tc.precomp.instance.is-uvar f => 
      sigma T\
        tc.precomp.instance {{c1 (fun x y => lp:f y x)}} T N,
        std.assert! (T = app[{{c1}}, tc.maybe-eta-tm _ _]) "[TC] invalid precomp".
  }}.

  Instance a1 : forall (F : Type -> Type -> Type), 
    c2 (fun x y => F y x) -> c1 F. Qed.

  Instance b1 : c2 f. Qed.

  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_swap.

Module HO_5.
  Axiom (f : Type -> Type -> Type).

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).
  Class c3 (T : (Type -> Type -> Type)).

  Instance a1 : forall (F : Type -> Type -> Type), 
    (c2 (fun x y => F y x) -> c3 (fun x y => F y x)) -> c1 F. Qed.

  Instance a2 : c2 f -> c3 f. Qed.

  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_5.


Module HO_6.
  Axiom (f : Type -> Type -> Type).

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).
  Class c3 (G : nat -> nat) (T : (Type -> Type -> Type)).

  Instance a1 : forall (F : Type -> Type -> Type), 
    (c2 (fun x y => F y x) -> 
      forall G, c3 G (fun x y => F y x)) -> 
    c1 F. 
  Qed.

  Instance a2 : forall F, c2 f -> c3 F f. Qed.

  Goal c1 (fun x y => f y x).
    apply _.
  Qed.
End HO_6.

Module HO_7.
  (* Here maybe-eta is in the goal, with a flexible head *)
  Axiom f : Type -> Type -> Type.
  Class c1 (T : Type -> Type -> Type) (T : Type -> Type -> Type).
  Instance i1: c1 f (fun x y => f y x). Qed.

  (* 
    TODO: decl M _ {{Type -> Type -> Type}} => coq.typecheck M Ty ok.
      Ty is flex, I would like it to be (prod _ _ (x\ prod _ _ _)))
      to make the following test succeed
    Elpi Query TC.Solver lp:{{
    decl M _ {{Type -> Type -> Type}} =>
      tc.compile.goal {{c1 (fun x y => lp:M y x) lp:M}} G L,
      std.length L Len,
      std.assert! (Len = 5).
  }}. *)

  Goal exists M, c1 (fun x y => M y x) M. 
    eexists.
    apply _.
  Qed.
End HO_7.

Module HO_81.
  Class c1 (T : Type).
  Instance i1 F : c1 F. Qed.

  Elpi Accumulate TC.Solver lp:{{
    :before "compile-goal"
    tc.compile.goal Goal _ _ :-
      Goal = {{HO_81.c1 lp:_}}, !,
      tc.precomp.goal Goal _ Vars, !,
      tc.compile.goal.make-pairs Vars Pairs,
      std.assert! (Pairs = []) "".
  }}.
  Elpi Typecheck TC.Solver.

  Goal exists X, c1 X.
    eexists.
    (* Fail is good, since here we simply check that the number of 
      uvar-pair built by tc.precomp is zero. This is because the type
      of ?X is Type (i.e. it has `arity` zero) *)
    Fail apply _.
  Abort.
End HO_81.

Module HO_8.
  Class c1 (T : Type -> Type -> Type).
  Instance i1 F : c1 (fun x => F x). Qed.

  Goal exists X, c1 X.
    eexists.
    apply _.
    Unshelve.
    apply nat.
  Qed.
End HO_8.

Module HO_9.
  Axiom f : Type -> Type -> Type.

  Class c1 (T : Type -> Type).
  Instance i1 A: c1 (fun x => f (A x) (A x)). Qed.

  Elpi Query TC.Solver lp:{{
    pi F\ sigma T\ decl F `x` {{Type -> Type}} => tc.precomp.instance.is-uvar F => 
      tc.precomp.instance {{c1 (fun x => f (lp:F x) (lp:F x))}} T N,
      std.assert! (T = app [{{c1}}, tc.maybe-eta-tm _ _]) "Invalid precompilation".
  }}.

  Goal exists X, c1 X.
    eexists.
    apply _.
    Unshelve.
    apply H.
  Qed.
End HO_9.

Module HO_scope_check1.
  Axiom f : Type -> (Type -> Type) -> Type.
  Axiom g : Type -> Type -> Type.
  Axiom a : Type.

  Class c1 (T : Type -> Type).

  Instance i1 : forall X, c1 (fun x => f x (fun y => g x (X y))). Qed.

  Goal c1 (fun x => f x (g x)).
    apply _.
  Qed.

  Elpi Query TC.Solver lp:{{
    sigma X Q\ % To avoid printing in console
      build-query-from-goal {{c1 (fun x => f x lp:X)}} _ Q _,
      coq.say Q,
      (pi A L T\ 
        tc.link.scope-check (uvar _ L) (fun _ _ (x\ app [{{g}}|_] as T)) :- !, 
          std.assert! (not (prune A L, A = T)) "[TC] Should fail by Scope Check", 
          fail) =>
      not Q.
  }}.

  (* Here fail on scope check *)
  Goal exists X, c1 (fun x => f x X).
    eexists.
    Fail apply _.
  Abort.
End HO_scope_check1.

Module beta_reduce_preprocess.
  Axiom f : Type -> Type -> Type.

  Module in_instance.
    Class c1 (T:Type).
    Instance i1 : c1 ((fun x y => f y x) nat bool). Qed.
    
    Goal c1 (f bool nat).
      apply _.
    Qed.
  End in_instance.

  Module in_goal.
    Class c1 (T : Type).
    Instance i1 : c1 (f nat bool). Qed.
    Goal c1 ((fun x y => f y x) bool nat).
      apply _.
    Qed.
  End in_goal.
End beta_reduce_preprocess.

Module Llam_1.

  Class A (i: nat -> nat).
  Class B (i: nat -> nat).

  Elpi Query TC.Solver lp:{{
    @pi-decl `x` {{Type -> Type}} f\ tc.precomp.instance.is-uvar f => 
      @pi-decl `x` {{Type -> Type}} g\ tc.precomp.instance.is-uvar g => 
        sigma T\
          tc.precomp.instance {{A (fun x => lp:f (lp:g x))}} T N,
          std.assert! (T = app[{{A}}, tc.maybe-eta-tm (fun _ _ (x\ tc.maybe-llam-tm _ _)) _]) "[TC] invalid precomp".
  }}.

  Instance I1: forall F G, B G -> A (fun x => F (G x)). Qed.
  Instance I2: B (fun x => x). Qed.

  (* HERE progress-llam-refine! *)
  (* While back-chaining `I1`, the eta-link for `F (G x)` is triggered,
     and the `llam-link` for `F (G x)` becomes `S =llam F (G x)`
     the premise `B G` assigns `G` to the identity (thanks to I2),
     this updates the `llam-link` to `S = llam F x`. 
     `F x` is in PF, and can safely be unfied to `S`.
     The finaly substitution is therefore: I1 S (fun x => x) I2 *)
  Goal A S.
    apply _.
  Qed.

End Llam_1.

Module Llam_2.
  Axiom a : nat.

  Class c1 (i: nat).
  Class c2 (i: nat -> nat).

  Instance I1: forall F, c2 F -> c1 (F a). Qed.
  Instance I2: c2 (fun x => x). Qed.

  (* HERE progress-rhs! *)
  (* While back-chaining, the goal unify with I1. 
    `c2 F` is unified with `c2 (fun x => x)` due to I2.
    F is now rigid can be beta-reduced to a *)
  Goal c1 a.
    apply _.
  Qed.

  Goal exists X, c1 X.
    eexists.
    apply _.
  Qed.
End Llam_2.

Module Llam_3.
  Axiom f: bool -> unit -> nat -> nat -> nat -> nat.
  Class c1 (i : nat).
  Class c2 (i: nat).
  Class c3 (i: bool -> unit -> nat -> nat -> nat -> nat).
  Instance I1 : forall (F: bool -> unit -> nat -> nat -> nat) G, 
    c3 G ->
    (forall a b c d, c2 (G a b c d (F a b c d))) -> c1 0. Qed.

  Instance I2 : c3 f. Qed.
  Instance I3 a b c d F: c2 (f a b c d F). Qed.
  
  Goal c1 0.
    apply _.
    Unshelve.
    apply H1.
  Qed.
End Llam_3.

Module CoqUvar.
  Class c1 (i:Type -> Type -> Type).

  (* TODO: this should pass *)
  Goal exists F, c1 (fun x y => F y x) -> c1 F.
    (* exists (fun x y => nat); auto. *)
    eexists.
    intros.
    Fail apply _.
  Abort.
End CoqUvar.

Module CoqUvar1.
  Class c1.
  Class c2 (i:Type -> Type -> Type).

  Axiom f : Type -> Type -> Type.

  Instance i1: c2 f -> c1. Qed.

  (* TODO: this should pass *)
  Goal exists F, c2 (fun x y => F y x) -> c1.
    (* exists (fun x y => f y x); apply i1. *)
    eexists.
    intros.
    Fail apply _.
  Abort.
End CoqUvar1.
