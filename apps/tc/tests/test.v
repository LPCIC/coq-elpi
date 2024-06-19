From elpi Require Import tc.

Section test_max_arity.
  Elpi Query TC.Solver lp:{{
    T = (c1\ prod `c` _ c2 \
      prod `_` 
        (prod `a` _ c3 \
          app [global _, app [c1, c3], c2]) c3 \
        app [global _, c1, c2]),
    pi x\ tc.precomp.instance.get-range-arity x _ (T x) (r-ar z (s z)).
  }}.
End test_max_arity.

Module test_link_eta_generation.
  Class c (T : Type -> Type -> Type -> Type).
  Class d (T : Type) (T : Type -> Type -> Type -> Type).
  Elpi Accumulate TC.Solver lp:{{
    :after "0" 
    tc.compile.instance.compile-conclusion _ (app [H|_]) _ _ _ Premises _ :-
      H = {{test_link_eta_generation.c}}, !,
      std.assert! (Premises = [do [tc.link.eta _ _] | _]) "[TC] Wrong number of eta links",
      coq.say "Good padding from here",
      fail.
  }}.
  Elpi Query TC.Solver lp:{{
    ToCompile = {{forall (T : Type -> Type -> Type -> Type), (forall (a: Type), d a T) -> c T}},
    not (tc.compile.instance ToCompile _ _).
  }}.
End test_link_eta_generation.

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
    tc.link.eta.maybe-eta (fun `x` _ c0 \ fun `y` _ c1 \ A2 c1 c0),
    tc.link.eta.maybe-eta (fun `x` _ c0 \ fun `y` _ c1 \ A2 (A c1) c0),
    tc.link.eta.maybe-eta {{fun x y => f x y}}.
  }}.

  Class c1 (T : (Type -> Type -> Type)).
  Class c2 (T : (Type -> Type -> Type)).

  Elpi Query TC.Solver lp:{{
    @pi-decl `x` {{Type -> Type}} f\ tc.precomp.instance.is-uvar f => 
      sigma T\
        tc.precomp.instance {{c1 (fun x y => lp:f y x)}} T N _ _,
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
      std.assert! (Pairs = []) "", fail.
  }}.
  Elpi Typecheck TC.Solver.

  Goal exists X, c1 X.
    eexists.
    (* Failure is good, since here we simply check that the number of 
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
      tc.precomp.instance {{c1 (fun x => f (lp:F x) (lp:F x))}} T N _ _,
      std.assert! (T = app [{{c1}}, tc.maybe-eta-tm _ _]) "Invalid precompilation".
  }}.

  Goal exists X, c1 X.
    eexists.
    (* TODO: here good solution, but universe problem!!! *)
    eapply (i1 (fun x => _)).
    (* apply _. *)
    Unshelve.
    auto.
  Qed.
End HO_9.

Module HO_10.
  Axiom f : Type -> Type -> Type.

  Class c1 (T : Type -> Type -> Type).
  Instance i1 A: c1 (fun x y => f (A x y) (A x y)). Qed.

  (* Note: here interesting link-dedup *)
  Goal exists X, c1 X.
    eexists.
    (* TODO: here good solution, but universe problem!!! *)
    (* apply _. *)
    eapply (i1 (fun _ _ => _)).
    Unshelve.
    auto.
  Qed.
End HO_10.

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
          tc.precomp.instance {{A (fun x => lp:f (lp:g x))}} T N _ _,
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
    (* Note : if, as coq, we force the llam link immediately, then apply _ fails *)
    Fail apply _.
  Abort.

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
    auto.
  Qed.
End Llam_3.

Module Llam_4.
  Axiom f : Type -> (Type -> Type) -> Type.
  Axiom g : Type -> Type -> Type.
  Axiom a : Type.

  Class c1 (T : Type -> Type).

  Instance i1 : forall X, c1 (fun x => f x (X x (fun (_: nat) => a) x)). Qed.

  Fail Elpi Query TC.Solver lp:{{
    sigma X Q\ % To avoid printing in console
      build-query-from-goal {{c1 (fun x => f x lp:X)}} _ Q _,
      not Q.
  }}.
End Llam_4.

Module Llam_5.
  Definition NN := nat -> nat.
  Class c1 (T : nat).
  (* Instance has a uvar whose type is hidden behind a definition *)
  Instance i : forall (x : NN), c1 (x 3). Qed.

  Goal c1 (id 3).
    apply _.
  Qed.
End Llam_5.

Module Llam_6.

  Class B (i: nat -> nat -> nat).

  Elpi Query TC.Solver lp:{{
    (pi x\ tc.unify-eq {{fun _ => 0}} (P x x)),
    coq.say (P {{1}} {{2}}),
    std.assert! (P {{1}} {{2}} = {{ fun _ => 0}}) "Heuristic error". 
  }}.

  Axiom (f : nat -> nat).
  Instance instB: B (fun _ _ => f 3) := {}.

  Class A.
  Instance instA : forall X, B (fun x => X x x) -> A := {}.

  Goal A.
    apply _.
  Qed.

End Llam_6.

Module CoqUvar.
  Class c1 (i:Type -> Type -> Type).

  Elpi Query TC.Solver lp:{{
    tc.precomp.instance {{c1 (fun x y => lp:F y x)}} T _ _ _,
    coq.say T,
    Expected = app[{{c1}}, tc.maybe-eta-tm (fun _ _ Inn) []],
    std.assert! (T = Expected) "[TC] invalid precompile1",
    pi x\ sigma ExpectedInn\
      ExpectedInn = tc.maybe-eta-tm (A x) [x],
      std.assert! ((Inn x) = ExpectedInn) "[TC] invalid precompile2".
  }}.

  Goal exists F, c1 (fun x y => F y x) -> c1 F.
    (* exists (fun x y => nat); auto. *)
    eexists.
    apply _.
    Unshelve.
    apply nat.
  Qed.
End CoqUvar.

Module CoqUvar1.
  Class c1.
  Class c2 (i:Type -> Type -> Type).

  Axiom f : Type -> Type -> Type.

  Instance i1: c2 f -> c1. Qed.

  Goal exists F, c2 (fun x y => F y x) -> c1.
    (* exists (fun x y => f y x); apply i1. *)
    eexists.
    intros.
    apply _.
  Qed.
End CoqUvar1.

Module CoqUvar2.
  Axiom t : Type.
  Class c1 (T : Type).
  Instance i1 (F: Type -> Type): c1 (F t). Qed.

  Goal exists F, c1 (F t).
    eexists.
    (* Set Debug "unification". *)
    (* TODO: here we produce a eta-expanded proof, which produce a coq unification between `?F a` and `fun x => X x`
             if we eta-reduce then coq has to unify `?F a` against `X` which succeeds *)
    apply _.
Fail Check (i1 (fun x => _)) : c1 ( (fun x => _) t). (* ??? *)
    Unshelve.
    auto.
  Qed.
End CoqUvar2.


Module CoqUvar3.
  Axiom f : Type -> Type -> Type.

  Class c1 (T : Type -> Type -> Type).
  Instance i1 A: c1 (fun x y => f (A x y) (A x y)). Qed.
  
  Elpi Query TC.Solver lp:{{
    tc.precomp.goal {{c1 (fun x y => lp:X (lp:A x y) y)}} C _,
    Expected = app [{{c1}}, tc.maybe-eta-tm (fun _ _ Body1) _],
    Body1 = (x\ tc.maybe-eta-tm (fun _ _ (Body2 x)) [x]),
    Body2 = (x\y\ tc.maybe-llam-tm (app [app [X], (Y x y), y]) [x,y]),
    std.assert! (C = Expected) "[TC] invalid compilation".
  }}.

  (* Note: here interesting link-dedup *)
  Goal exists X (A: Type -> Type -> Type), c1 (fun x y => X (A x y) y).
  (*
    do 2 eexists.
    apply _.
    Show Proof.
    Unshelve.
    apply T. apply T.
    Show Proof. *) (* proof is OK, but for universes!!!! *)
    apply (ex_intro
   (fun X : Type -> Type -> Type =>
	exists A : Type -> Type -> Type, c1 (fun x y : Type => X (A x y) y))
   (fun _ H : Type => f H H)
   (ex_intro
      (fun A : Type -> Type -> Type =>
       c1 (fun x y : Type => (fun _ H : Type => f H H) (A x y) y))
      (fun H _ : Type => H) (i1 (fun _ H : Type => H)))).
  Qed.

  Axiom g : Type -> Type -> Type.
  (* Note: here interesting failing link-dedup *)
  Goal exists (A: Type -> Type -> Type), c1 (fun x y => g (A x y) y).
    do 1 eexists.
    Fail apply _.
  Abort.
End CoqUvar3.

Module CoqUvar4.
  Axiom f : Type -> Type -> Type.

  Class c1 (T : Type -> Type -> Type).
  
  Elpi Query TC.Solver lp:{{
    tc.precomp.instance {{c1 (fun x y => lp:X (lp:A x y) y)}} C _ _ _,
    Expected = app [{{c1}}, tc.maybe-eta-tm (fun _ _ Body1) _],
    Body1 = (x\ tc.maybe-eta-tm (fun _ _ (Body2 x)) [x]),
    Body2 = (x\y\ tc.maybe-llam-tm (app [app [X], (Y x y), y]) [y,x]),
    std.assert! (C = Expected) "[TC] invalid compilation".
  }}.

  (* Note: here interesting failtc-c1ing link-dedup *)
  Goal forall f, exists X, c1 (X nat) -> 
    c1 (f nat nat).
    do 1 eexists.
    apply _.
  Qed.
End CoqUvar4.

(* TODO: add test with negative premise having a variable with type (M A) where M and A are coq uvar,
         this is in order to clean-term with llam *)