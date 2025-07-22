From elpi.apps Require Import derive.std rbuild.

Record foo {A} := { a : nat; b : bool; c : A }.
#[only(lens)] derive foo.

(* Build a record without mentioning its constructor name *)
Check « 3 ; false; tt » : foo.

(* This time using labels to change the order of fields *)
Check « false ; a := 1 + 2; tt » : foo.
Check « c := tt ; a := 1 + 2; false » : foo.

(* This time ; _ enables padding *)
Check « c := tt ; _ » : foo.

(* No type annotation but label *)
Check « c := tt; _ ».

(* Update with a lens *)
Check fun x : foo =>
  « x with a := 3 ».

(* Errors: *)
Fail Check « c := tt ». (* Error: not enough fields, maybe use « ... ; _ » *)
Fail Check « c := tt; 1; 2; 3; 4 ». (* Error: too many fields *)
Check « false ».  (* « unresolved record » *)
Fail Check « c := tt; 1; 2 ». (* Error:
    Illtyped record: Illegal application: 
    The term "Build_foo" of type "forall A : Type, nat -> bool -> A -> foo"
    cannot be applied to the terms
    "?e0" : "Type"
    "1" : "nat"
    "2" : "nat"
    "tt" : "unit"
    The 3rd term has type "nat" which should be a subtype of "bool". *)

Record bar := { f : @foo nat; d : nat }.
#[only(lens)] derive bar.
Record baz := { w : bar }.
#[only(lens)] derive baz.

(* Update with a composed lens *)
Check fun x : baz =>
  « x with w#f#c := 3 ».

(* # is just catcomp from ssrfun *)
Import ssrfun.
Check fun x : baz =>
  « x with (w \; f \; c) := 3 ».



