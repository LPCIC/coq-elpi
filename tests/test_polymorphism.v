From elpi Require Import elpi.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.
Set Debug "comInductive".
Set Debug "elpi".

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

Set Debug "ustate".
Set Debug "univVariances".
Set Debug "univMinim".
Module test_explicit.
Elpi Command test_explicit.
Elpi Query lp:"
   @keep-alg-univs! => @univpoly! => @cumulative! => coq.env.add-indt (record ""test"" {{Type}} ""mktest""
     (field _ ""foo"" {{Type}}  _ \ end-record)) _C.
".
Print test.
(* Record test@{u u0} : Type@{u} := mktest { foo : Type@{u0} }. *)
(* u(= (* for typing) in term, + in type) u0(= in term) |= u0 < u *) *)
(* It's indeed polymorphic but we do not get the minimized version *)
End test_explicit.

Module test_minimization.
Elpi Command test_minimization.
Elpi Query lp:"
   coq.univ.new U,
   coq.univ.variable U V,
   @keep-alg-univs! => @udecl! [V] ff [] tt => coq.env.add-indt (record ""test"" (sort (typ _)) ""mktest""
     (field _ ""foo"" (sort (typ U))  _ \ end-record)) _C.
".
Print test.
(* It's indeed polymorphic but we do not get the minimized version *))
End test_minimization.