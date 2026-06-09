From elpi Require Import tc.


Set TC NameShortPath.
Class C (T : Type) := {f : T -> T}.
Record r := mkr {car : Type; rf : car -> car}.
Canonical Structure c := mkr nat (fun x => x).

Elpi Accumulate TC.Compiler lp:{{
  % the goal is to check instances for C are correctly compiled
  func is-class-C prop ->.
  is-class-C (pi x\ X x) :- !, pi x\ is-class-C (X x).
  is-class-C (tc-C _ _ :- _ as C) :- !, coq.say "Checking"C, if (expected-rule C) true (coq.error "Wrong compilation of" C).
  is-class-C (tc-C _ _ as C) :- !, coq.say "Checking"C, if (expected-rule C) true (coq.error "Wrong compilation of" C).
  is-class-C _.


  func expected-rule -> prop.
  pred dummy.
  :name "x" dummy.
  :before "tc-adder"
  tc.add-tc-db _I _G C :- % coq.say "Compiled term is" C,
    std.spy(is-class-C C), fail, !.
}}.

Module m1.
  Elpi Accumulate TC.Compiler lp:{{
    :after "x" expected-rule (tc-C {{nat}} _).
  }}.

  (* reducing the projection statically *)
  Local Instance inst_red: C (car c). now constructor. Qed.

  Elpi Accumulate TC.Compiler lp:{{
    % removing the previous expected (best should be that the previous rule is local to the module)
    :after "x" expected-rule _ :- !, fail.
  }}.
  (* Elpi Print TC.Compiler "elpi.apps.derive.tests/xxx".  *)

  Goal C nat. apply _. Qed.
  Goal C (car c). apply _. Qed.
End m1.

Module m2.
  (* Mh, why this fails? *)
  (* Elpi Accumulate TC.Compiler lp:{{
    :after "x" expected-rule X :- !, coq.say "CIAO"X, std.spy(X = (tc-C Y _ :- [tc.link.proj _ _])), !.
  }}. *)
  Elpi Accumulate TC.Compiler lp:{{
    % TODO: here I am doing to weak check, should make the previous Accumulate succeeds
    :after "x" expected-rule X :- !, X = (tc-C Y _ :- [K_]), !.
  }}.

  (* cannot reduce the projection: c is quantified *)
  Local Instance inst c: C (car c). now constructor. Qed.

  (* need to use the chr *)
  Goal C nat. apply _. Qed.
  Goal C (car c). apply _. Qed.
End m2.


Module m3.
  Elpi Accumulate TC.Compiler lp:{{
    % TODO: here I am doing to weak check, should make the previous Accumulate succeeds
    :after "x" expected-rule (tc-C X _) :- !, name X.
  }}.

  (* cannot reduce the projection: c is quantified *)
  Instance inst X: C X. now constructor. Qed.

  (* need to use the chr *)
  Goal C nat. apply _. Qed.
  Goal C (car c). apply _. Qed.
  (* with local instance for c *)
  Goal forall x, C (car x). apply _. Qed.
End m3.
