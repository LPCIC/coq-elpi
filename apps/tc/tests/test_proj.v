From elpi Require Import tc.
From elpi Require Import elpi.

Global Set TC NameShortPath.
Class C (T : Type) := mkC {f : T -> T}.
Class D (T : nat -> nat) := {g : unit}.
Class E (T : nat) := {ge : unit}.
Record r := mkr {car : Type; #[canonical=no] rf : car -> car}.
Canonical Structure c := mkr nat (fun x => x).


(* Elpi cs default (r). *)
Elpi cs cs (c).

Elpi Accumulate TC.Compiler lp:{{
  % the goal is to check instances for C are correctly compiled
  func is-class-C prop ->.
  is-class-C (pi x\ X x) :- !, pi x\ is-class-C (X x).
  is-class-C (tc.instance _ _ _ _) :- !.
  :name "is-class-C"
  is-class-C (tc.class _ _ _ _) :- !.
  is-class-C C :- 
    coq.error 
      "Fail to verify the shape of compiled instance."
      "Received:\n" C 
      "\nTo fix the issue either the class is compiled wrongly\n" 
      "or you forgot to load. A is-class-C rule in the database".

  :before "tc-adder"
  tc.add-tc-db _I _G C :- % coq.say "Compiled term is" C,
    is-class-C C, fail, !.
}}.

Module m1.
  Elpi Accumulate TC.Compiler lp:{{
    :after "is-class-C" is-class-C (tc-C {{nat}} _) :- !.
  }}.

  (* reducing the projection statically *)
  Local Instance inst_red: C (car c). now constructor. Qed.

  Elpi Accumulate TC.Compiler lp:{{
    % removing the previous expected (best should be that the previous rule is local to the module)
    :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !.
  }}.
  (* Elpi Print TC.Compiler "elpi.apps.derive.tests/xxx".  *)

  Goal C nat. apply _. Qed.
  Goal C (car c). apply _. Qed.
End m1.

Module m1'.
  Elpi Accumulate TC.Compiler lp:{{
    % NOTE: rf is not canonical, therefore no reduced nor linked
    :after "is-class-C" is-class-C (tc-D {{rf c}} _) :- !.
  }}.

  Local Instance inst_red: D (rf c). now constructor. Qed.

  Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !. }}.
  (* NOTE: The failure here is due to delta and beta conversion rules *)
  Goal D (fun x => x). Fail apply _. Abort.
End m1'.

Module m1''.
  Elpi Accumulate TC.Compiler lp:{{
    :after "is-class-C" is-class-C (tc-E {{rf c 3}} _) :- !.
  }}.

  Local Instance inst_red: E (rf c 3). now constructor. Qed.
  Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !. }}.

  (* NOTE: similarly to previous test, this fails due to delta-beta conv rules *)
  Goal E 3. Fail apply _. Abort.
End m1''.

Module m2.
  Elpi Accumulate TC.Compiler lp:{{
    :after "is-class-C" is-class-C (tc-C X (app[_,W]) :- [tc.link.proj CAR X W]) :- !, const CAR = {{:gref car}}, name X.
  }}.

  (* cannot reduce the projection: c is quantified *)
  Local Instance inst c: C (car c). now constructor. Qed.
  Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !. }}.

  (* need to use the chr *)
  Goal C nat. apply _. Qed.
  Goal C (car c). apply _. Qed.
End m2.


Module m3.
  Elpi Accumulate TC.Compiler lp:{{
    :after "is-class-C" is-class-C (tc-C X _) :- !, name X, coq.say K_.
  }}.

  (* cannot reduce the projection: c is quantified *)
  Local Instance inst X: C X. now constructor. Qed.
  Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !. }}.

  (* need to use the chr *)
  Goal C nat. apply _. Qed.
  Goal C (car c). apply _. Qed.
  (* with local instance for c *)
  Goal forall x, C (car x). intros. apply _. Qed.
End m3.

Module m4.
  (* test using primitive projection and parametrized record *)
  Set Primitive Projections.
  Record ofe (SI : Type) := Ofe {
    ofe_car1 :> Type;
    ofe_car2 :> Type -> Type;
  }.

  Canonical Structure ss := Ofe nat nat (fun x => x).

  Definition p := Ofe nat bool (fun x => x).

  Check (eq_refl : (p.(ofe_car1 _)) = bool).

  Elpi Query TC.Solver lp:{{
    % destruct application with primitive projection
    % and retrieving the projector number and the record constant
    app[primitive (proj P N), (global (const X))] = {{p.(ofe_car1 _)}},
    % get the body of the constant
    coq.env.const X (some (app[H | Args])) XTy,
    coq.safe-dest-app XTy _ XTyAg,
    % getting the projection of the constant
    std.assert! (std.nth N Args {{bool}}) "Invalid proj",
    % creating a rocq-term in elpi equivalent to the original one
    % but using its canonical projection
    coq.env.primitive-projection? P C _,
    std.append ([global (const C) | XTyAg]) [global (const X)] RR,
    std.assert-ok!(coq.typecheck (app RR) _) "error",
    true.
  }}.

  (* Elpi Accumulate TC.Compiler lp:{{
    :after "x" expected-rule (tc-C N (app[_, N])) :- !, name N.
  }}. *)

  Local Instance inst2 c: C c. now constructor. Qed.

  Goal forall x y, C (@ofe_car1 x y). apply _. Qed.

  Goal forall x y, C (@ofe_car2 x y x). apply _. Qed.
End m4.

(* Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C _ :- !. }}. *)
Set Printing All.

Module M.

  Definition fcs1 (H1 H2 : r) := (fun '(x,y) => (rf H1 x, rf H2 y)).
  Local Canonical Structure cs1 (H1 H2 H3 : r) := mkr (car H1 * car H2) (fcs1 H1 H2).

  Goal exists x, car x = (nat * nat)%type.
  Proof. eexists. auto. Unshelve. apply c. Qed.

  Local Canonical Structure cs2 (T : Type) (c : C T) := mkr T (@f _ c).

  Local Instance i : C bool. apply (mkC _ (fun x => x)). Qed.

  Elpi Accumulate solve_cs lp:{{
    solve (goal _ _ {{@eq lp:T_ lp:P lp:T}} _ _ as G) GL :-
      % coq.say "The goal is"G,
      P = app [global (const Proj), A],
      cs.compiler.cs.compiler ff (pr 0 Proj) A (app[_, T]) [] [] [] R,
      % R, coq.say "The rule is"R,
      @no-tc! => refine {{eq_refl}} G GL.
  }}.

  Goal exists x, car x = bool.
  Proof. 
    eexists.
    elpi solve_cs.
  Abort. (*TODO:*)
End M.

Module M1.
  Class C (T : Type) := {f : T -> Prop}.
  Local Instance i x : C (car x). Admitted.
  Check (_ : C (car _)).
End M1.

Module M2.
  Inductive to_prop (T: Type) : Prop := tp : T -> to_prop T.

  Record r1 := mkr1 {car : Type; #[canonical=no] rf : C car}.
  Local Instance i : C bool. Admitted.
  Local Canonical Structure c1 := mkr1 bool i.
  Elpi cs cs (c1).

  Goal exists x, to_prop (C (car x)).
  Proof. 
    eexists; constructor.
    apply _.
  Qed.
End M2.

Module M3.

  Set Printing All.
  Structure set (T : Type) := MkSet {
    set_to_pred : T -> Prop
  }.
  Arguments set_to_pred : simpl never.

  Class mem T X (x : T) := mkMem { IsMem : set_to_pred _ X x }.

  (* memType is the type of elements of a given set. *)
  Module Mem.
  Record type T (X : set T) := Pack { elt : T;   memP : mem _ X elt }.
  End Mem.

  (* Canonical Structure s T X E (I: @mem T X E) := Mem.Pack _ _ _ I. *)
  Elpi cs cs (Mem.Pack).

  Elpi Accumulate TC.Compiler lp:{{
    :after "is-class-C" is-class-C (tc-mem Ty S T {{@Mem.memP lp:Ty lp:S lp:Z}} :- [tc.link.proj X T Z]) :- !,
      const X = {{:gref Mem.elt}}.
  }}.

  Existing Instance Mem.memP.

  Elpi Print TC.Compiler "elpi.apps.derive.tests/xxx". 

End M3.