From elpi Require Import elpi.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Module test_rocq.
Record test : Type := mktest { foo : Type }.
Print test. (* Record test@{u} : Type@{u+1} := mktest { foo : Type@{u} }. (* u |=  *)*)
End test_rocq.
Module test_elpi.
Elpi Command test_default.
Elpi Query lp:"
   coq.env.add-indt (record ""test"" {{Type}} ""mktest""
     (field _ ""foo"" {{Type}}  _ \ end-record)) _C.
".
Print test. (* Record test : Type@{test.u0} := mktest { foo : Type@{test.u1} }. *)
(* we get a monomorphic universe *)
End test_elpi.

Module test_explicit.
Elpi Command test_explicit.
Elpi Query lp:"
   @keep-alg-univs! => @univpoly-cumul! => coq.env.add-indt (record ""test"" {{Type}} ""mktest""
     (field _ ""foo"" {{Type}}  _ \ end-record)) _C.
".
Print test.
(* Record test@{u} : Type@{u+1} := mktest { foo : Type@{u} }. *)
(* u(+ (= for typing) in term, + in type) |= *)
(* It's indeed polymorphic and we do get the minimized version *)
End test_explicit.

Module test_explicit2.
Elpi Command test_explicit2.
Elpi Query lp:"
  coq.univ.new U,
   @keep-alg-univs! => @univpoly-cumul! =>
    coq.env.add-indt (record ""test"" (sort (typ U+1)) ""mktest""
     (field _ ""foo"" (sort (typ U))  _ \ end-record)) _C.
".
Print test.
(* Record test@{u} : Type@{u+1} := mktest { foo : Type@{u} }. *)
(* u(+ (= for typing) in term, + in type) |= *)
(* It's indeed polymorphic and we do get the minimized version *)
End test_explicit2.

Module test_minimization.
Elpi Command test_minimization.
Elpi Query lp:"
   coq.univ.new U,
   coq.univ.variable U V,
   @keep-alg-univs! => @udecl-cumul! [(auto V)] ff [] tt => coq.env.add-indt (record ""test"" (sort (typ _)) ""mktest""
     (field _ ""foo"" (sort (typ U))  _ \ end-record)) _C.
".
Print test.
(* It's indeed polymorphic and we do get the minimized version *)
End test_minimization.

Module test_cumul_def.
Elpi Command test_cumul_def.

Elpi Query lp:"
   coq.univ.new U,
   coq.univ.variable U V,
   @keep-alg-univs! => @udecl-cumul! [(auto V)] tt [] tt => coq.env.add-const ""polydef"" (sort (typ U)) _ _ _C.
".
  Print polydef.
Print test_cumul_def.
End test_cumul_def.
