From elpi Require Import tc.


Set TC NameShortPath.
Class C (T : Type) := {f : T -> T}.
Class D (T : nat -> nat) := {g : unit}.
Class E (T : nat) := {ge : unit}.
Record r := mkr {car : Type; rf : car -> car}.
Canonical Structure c := mkr nat (fun x => x).

Elpi Accumulate TC.Compiler lp:{{
  % the goal is to check instances for C are correctly compiled
  func is-class-C prop ->.
  is-class-C (pi x\ X x) :- !, pi x\ is-class-C (X x).
  :name "is-class-C"
  is-class-C (tc.instance _ _ _ _) :- !.
  % :name "XX"
  % is-class-C (tc-C _ _ :- _ as C) :- !, 
  %   coq.say "Checking"C, if (expected-rule C) true (coq.error "Wrong compilation of" C).
  % is-class-C (tc-C _ _ as C) :- !, 
  %   coq.say "Checking"C, if (expected-rule C) true (coq.error "Wrong compilation of" C).
  is-class-C C :- coq.error "FAIL" C.

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
    :after "is-class-C" is-class-C (tc-D {{fun x => x}} _) :- !.
  }}.

  Local Instance inst_red: D (rf c). now constructor. Qed.

  Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !. }}.
  Goal D (fun x => x). apply _. Qed.
End m1'.

Module m1''.
  Elpi Accumulate TC.Compiler lp:{{
    :after "is-class-C" is-class-C (tc-E X _ :- [K_]) :- !, name X.
  }}.

  (* TODO: the current compiler is too permessive: it replaces rf c 3 *)
  (* which contains 1. record reduction 2. beta reduction *)
  (* two solutions 1. avid to define a class like that one 2. correctly reduce *)
  Local Instance inst_red: E (rf c 3). now constructor. Qed.
  Elpi Accumulate TC.Compiler lp:{{ :after "is-class-C" is-class-C C :- coq.error "FAIL" C, !. }}.

  Goal E 3. apply _. Qed.
End m1''.

Module m2.
  (* Mh, why this fails? *)
  (* Elpi Accumulate TC.Compiler lp:{{
    :after "x" expected-rule X :- !, coq.say "CIAO"X, std.spy(X = (tc-C Y _ :- [tc.link.proj _ _])), !.
  }}. *)
  Elpi Accumulate TC.Compiler lp:{{
    % TODO: here I am doing to weak check, should make the previous Accumulate succeeds
    :after "is-class-C" is-class-C (tc-C X _ :- [K_]) :- !, name X, coq.say K_.
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
  Elpi Trace Browser.
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

  Goal forall x y, C (@ofe_car1 x y).
    intros x y. apply _. Qed.

  Goal forall x y, C (@ofe_car2 x y x).
    intros x y. apply _. Qed.
End m4.

From elpi.apps Require Import db.

From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
From elpi.apps.tc.elpi Extra Dependency "cs.elpi" as cs.
Elpi Command B.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
(* Elpi Accumulate File base. *)
Elpi Accumulate File tc_aux.
Elpi Accumulate File cs.

Elpi Trace Browser.
Elpi Query lp:{{ cs.compiler.record.create-cs-pred {{r}}. }}.
Set Printing All.
Elpi Query lp:{{ cs.compiler.cs.main {{c}}. }}.

(* Elpi Print TC.Compiler "elpi.apps.derive.tests/xxx".  *)

Definition rrf (H1 H2 : r) := (fun '(x,y) => (rf H1 x, rf H2 y)).
Canonical Structure rr (H1 H2 H3 : r) := mkr (car H1 * car H2) (rrf H1 H2).

Elpi Trace Browser.
Elpi Query lp:{{ cs.compiler.cs.main {{rr}}. }}.

(* Elpi Print TC.Compiler "elpi.apps.derive.tests/xxx".  *)

Goal exists x, car x = (nat * nat)%type.
Proof. eexists. auto. Unshelve. apply c. Qed.