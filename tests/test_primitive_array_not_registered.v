From elpi Require Import elpi.

From Corelib Require Import PrimInt63.

(* PArray is deliberately NOT imported here: the array type is not
   registered, so building a nested primitive array (whose element type is
   itself the primitive array type) must fail with a clear kernel error,
   exactly like it already does for int63/float64/pstring when their own
   corelib module is not imported. *)

Fail Elpi Query lp:{{
  coq.primitive.array.make 1 (primitive (uint63 {coq.int->uint63 0})) Inner,
  coq.primitive.array.make 1 (primitive (array Inner)) _.
}}.
