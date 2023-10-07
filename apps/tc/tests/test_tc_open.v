From elpi.apps Require Import tc.
From Coq Require Import Arith ssreflect.

Ltac my_solver := trivial with arith.

Elpi Accumulate typeclass.db lp:{{

typeclass _ X Ty {{ @sig lp:Ty lp:P }} Solution :- std.do! [
  % we unfold letins since the solve is dumb
  (pi a b b1\ copy a b :- def a _ _ b, copy b b1) => copy X X1,
  % we build the solution
  Solution = {{ @exist lp:Ty lp:P lp:X1 _ }},
  % we call the solver
  coq.ltac.collect-goals Solution [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "my_solver") G [],
].

}}.
Elpi Typecheck typeclass.

Goal {x : nat | x > 0}.
apply: 3.
Qed.

Definition add1 n : {x : nat | x > 0} :=
  match n with
  | O => 1
  | S x as y => y
  end.
