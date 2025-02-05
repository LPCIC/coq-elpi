From elpi.apps Require Import derive.eqbOK.

From elpi.apps.derive.tests Require Import test_derive_corelib test_eqb test_eqbcorrect.

Import test_derive_corelib.Coverage 
       test_eqType_ast.Coverage
       test_eqb.Coverage
       test_eqbcorrect.Coverage.

Module Coverage.

Elpi derive.eqbOK empty.
Elpi derive.eqbOK unit.
Elpi derive.eqbOK peano.
Elpi derive.eqbOK option.
Elpi derive.eqbOK pair.
Elpi derive.eqbOK seq.
Elpi derive.eqbOK box_peano.
Elpi derive.eqbOK rose.
Elpi derive.eqbOK rose_p.
Elpi derive.eqbOK rose_o.
Fail Elpi derive.eqbOK nest.
Fail Elpi derive.eqbOK w.
Fail Elpi derive.eqbOK vect.
Fail Elpi derive.eqbOK dyn.
Fail Elpi derive.eqbOK zeta.
Elpi derive.eqbOK beta.
Fail Elpi derive.eqbOK iota.
(*
Elpi derive.eqbOK large.
*)
Elpi derive.eqbOK prim_int.
Fail Elpi derive.eqbOK prim_float.
Elpi derive.eqbOK fo_record.
Elpi derive.eqbOK pa_record.
Elpi derive.eqbOK pr_record.
Fail Elpi derive.eqbOK dep_record.
Elpi derive.eqbOK enum.
Fail Elpi derive.eqbOK eq.
Elpi derive.eqbOK bool.
Elpi derive.eqbOK sigma_bool.
Elpi derive.eqbOK ord.
Elpi derive.eqbOK ord2.
Elpi derive.eqbOK val.
Elpi derive.eqbOK alias.

End Coverage.

Import Coverage.

Redirect "tmp" Check peano_eqb_OK : forall n m, Bool.reflect (n = m) (peano_eqb n m).
Redirect "tmp" Check seq_eqb_OK : forall A eqA (h : forall a1 a2 : A, Bool.reflect (a1 = a2) (eqA a1 a2)) l1 l2, Bool.reflect (l1 = l2) (seq_eqb A eqA l1 l2).
Redirect "tmp" Check ord_eqb_OK : forall n (o1 o2 : ord n), Bool.reflect (o1 = o2) (ord_eqb n n o1 o2).
Redirect "tmp" Check alias_eqb_OK : forall x y : alias, Bool.reflect (x = y) (alias_eqb x y).
