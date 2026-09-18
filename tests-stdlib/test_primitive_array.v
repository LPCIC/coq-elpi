From elpi Require Import elpi.

From Corelib Require Import PrimInt63 PrimFloat PrimString.
From Stdlib Require Import PArray.

Open Scope uint63_scope.

(* round trip of real Coq array literals through embed + readback, via
   several distinct reduction strategies (mirrors the "primitive" tests for
   uint63/float64 in test_HOAS.v) *)
Module ArrHOAS.

Elpi Command primitive.
Elpi Accumulate lp:{{
main [trm T] :-
  std.assert! (coq.reduction.native.norm T _ T1) "normal form is not an opinion",
  std.assert! (coq.reduction.vm.norm T _ T1) "normal form is not an opinion",
  std.assert! (coq.reduction.cbv.norm T T1x) "normal form is not an opinion",
  std.assert! (T1x = T1) "normal form is not an opinion",
  std.assert! (coq.reduction.lazy.norm T T1) "normal form is not an opinion",
  std.assert! (coq.reduction.lazy.whd_all T T1) "normal form is not an opinion",
  coq.say "Raw term:" T "\nNice term:" {coq.term->string T} "\nRed:" {coq.term->string T1}.
}}.

Elpi primitive ([| 1; 2; 3 | 0 |] :> array int).
Elpi primitive ([| [| 1; 2 | 0 |]; [| 3 | 0 |] | [| | 0 |] |] :> array (array int)).

End ArrHOAS.

(* -- coq.primitive.array.* builtins: make/size/get/set/default/of-list/to-list -- *)

Elpi Command arr.basic.
Elpi Accumulate lp:{{
main _ :-
  U0 = {coq.int->uint63 0},
  coq.primitive.array.make 3 (primitive (uint63 U0)) A,
  std.assert! (coq.primitive.array.size A 3) "size",

  std.assert! (coq.primitive.array.get A 0 (primitive (uint63 U0))) "get default",

  U42 = {coq.int->uint63 42},
  coq.primitive.array.set A 1 (primitive (uint63 U42)) A1,
  std.assert! (coq.primitive.array.get A1 1 (primitive (uint63 U42))) "get after set",
  std.assert! (coq.primitive.array.get A1 0 (primitive (uint63 U0))) "get untouched",

  std.assert! (coq.primitive.array.dflt A1 (primitive (uint63 U0))) "default unaffected by set",

  coq.list->parray (primitive (uint63 U0)) [primitive (uint63 U42), primitive (uint63 U0)] A2,
  std.assert! (coq.parray->list A2 [primitive (uint63 U42), primitive (uint63 U0)]) "of-list/to-list".
}}.
Elpi arr.basic.

(* -- nested arrays -- *)

Elpi Command arr.nested.
Elpi Accumulate lp:{{
main _ :-
  U7 = {coq.int->uint63 7},
  coq.primitive.array.make 1 (primitive (uint63 U7)) Inner,
  coq.primitive.array.make 2 (primitive (array Inner)) Outer,
  std.assert! (coq.primitive.array.size Outer 2) "outer size",
  coq.primitive.array.get Outer 0 (primitive (array Inner1)),
  std.assert! (coq.primitive.array.get Inner1 0 (primitive (uint63 U7))) "inner get".
}}.
Elpi arr.nested.

(* -- out of bounds get/set -- *)

Elpi Command arr.oob.
Elpi Accumulate lp:{{
main _ :-
  U9 = {coq.int->uint63 9},
  coq.primitive.array.make 2 (primitive (uint63 U9)) A,
  std.assert! (coq.primitive.array.get A 10 (primitive (uint63 U9))) "get out of bounds returns default",
  coq.primitive.array.set A 10 (primitive (uint63 {coq.int->uint63 0})) A1,
  coq.parray->list A L,
  std.assert! (coq.parray->list A1 L) "set out of bounds is a no-op".
}}.
Elpi arr.oob.

(* -- fold / map -- *)

Elpi Command arr.foldmap.
Elpi Accumulate lp:{{

func sum-cb int, term, int -> int.
sum-cb _ (primitive (uint63 N)) Acc R :- coq.uint63->int N V, R is Acc + V.

func double-cb int, term -> term.
double-cb _ (primitive (uint63 N)) (primitive (uint63 N2)) :-
  coq.uint63->int N V, W is V * 2, N2 = {coq.int->uint63 W}.

main _ :-
  coq.list->parray (primitive (uint63 {coq.int->uint63 0}))
    [primitive (uint63 {coq.int->uint63 1}),
     primitive (uint63 {coq.int->uint63 2}),
     primitive (uint63 {coq.int->uint63 3})] A,
  coq.primitive.array.fold sum-cb A 0 Sum,
  std.assert! (Sum = 6) "fold sum",
  coq.primitive.array.map double-cb A A1,
  std.assert! (coq.parray->list A1
    [primitive (uint63 {coq.int->uint63 2}),
     primitive (uint63 {coq.int->uint63 4}),
     primitive (uint63 {coq.int->uint63 6})]) "map double".
}}.
Elpi arr.foldmap.

(* -- negative tests: heterogeneous arrays are rejected -- *)

Elpi Command arr.neg1.
Elpi Accumulate lp:{{
main _ :-
  coq.list->parray (primitive (uint63 {coq.int->uint63 0}))
    [primitive (float64 {coq.float->float64 1.0})] _.
}}.
Fail Elpi arr.neg1.

Elpi Command arr.neg2.
Elpi Accumulate lp:{{
main _ :-
  coq.primitive.array.make 1 (primitive (uint63 {coq.int->uint63 0})) A,
  coq.primitive.array.set A 0 (primitive (float64 {coq.float->float64 1.0})) _.
}}.
Fail Elpi arr.neg2.

(* -- negative test: a non-primitive term is not a valid element/default -- *)

Elpi Command arr.neg3.
Elpi Accumulate lp:{{
main _ :- coq.primitive.array.make 1 {{ true }} _.
}}.
Fail Elpi arr.neg3.
