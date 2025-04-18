From elpi.apps Require Import NES.

(* Some invalid namespaces *)
Fail NES.Begin.
Fail NES.Begin "".
Fail NES.Begin ".".
Fail NES.Begin ".A".
Fail NES.Begin "A.".
Fail NES.Begin "A..B".
Fail NES.Begin "A._.B".

(* name space creation *)
NES.Begin Foo.
Definition x := 3.
NES.End Foo.
Print Foo.x.

(* adding one name inside an existing name space *)
NES.Begin Foo.
Definition x2 := 4.
NES.End Foo.
Print Foo.x.
Print Foo.x2.

(* shadowing: adding the same name twice *)
NES.Begin Foo.
Definition x := 5.
NES.End Foo.
Check (refl_equal _ : Foo.x = 5). (* shadowing *)

(* nesting *)
NES.Begin A.
NES.Begin B.
Definition c := 1.
NES.End B.
NES.End A.
About A.B.c.

(* adding one name inside an existing, nested, name space *)
NES.Begin A1.
NES.Begin B1.
Definition c := 1.
NES.End B1.
NES.Begin B1.
Definition d := 1.
NES.End B1.
NES.End A1.
About A1.B1.d.
About A1.B1.c.

(* all names in the Foo namespace must be visible *)
NES.Open Foo.
Print x.
Print x2.

NES.Open A1.
Print B1.c.
Print B1.d.

NES.Open A1.B1.
Print d.

(* boh *)
NES.Begin A2.B2.
Definition e := 1.
NES.End B2.
NES.End A2.
NES.Begin A2.B2.
Definition f := 2.
NES.End A2.B2.
Print A2.B2.f.

NES.Begin X.
Module Y.
Fail NES.Begin Z.
End Y.
NES.End X.
