From elpi.apps Require Import derive.eqbcorrect.
From elpi.apps.derive Require Import param1. (* FIXME, the clause is in param1 *)
From elpi.apps.derive.tests Require Import test_derive_corelib test_eqType_ast test_tag test_fields test_eqb test_induction 
                                           test_param1 test_param1_trivial test_param1_functor.
Import test_derive_corelib.Coverage 
       test_eqType_ast.Coverage 
       test_tag.Coverage 
       test_fields.Coverage
       test_eqb.Coverage 
       test_induction.Coverage 
       test_param1.Coverage 
       test_param1_trivial.Coverage 
       test_param1_functor.Coverage.
    
Module Coverage.

(* Elpi Trace (* "derive.eqbcorrect.*" "derive.param1.functor.*" "correct-lemma-for" *) "param1-functor-for". *)
Elpi derive.eqbcorrect empty. 
Elpi derive.eqbcorrect unit. 
Elpi derive.eqbcorrect peano.
Elpi derive.eqbcorrect option.
Elpi derive.eqbcorrect pair.
Elpi derive.eqbcorrect seq.
Elpi derive.eqbcorrect box_peano.
Elpi derive.eqbcorrect rose.
Elpi derive.eqbcorrect rose_p.
Elpi derive.eqbcorrect rose_o.
Fail Elpi derive.eqbcorrect nest. (* Maybe fixable *)
Fail Elpi derive.eqbcorrect w.    (* Not fixable *)
Fail Elpi derive.eqbcorrect vect. (* Can be done *)
Fail Elpi derive.eqbcorrect dyn.  (* Not Fixable *)
Fail Elpi derive.eqbcorrect zeta. (* FIXME *)
Elpi derive.eqbcorrect beta.
Fail Elpi derive.eqbcorrect iota.
(*
Elpi derive.eqbcorrect large.
*)
Elpi derive.eqbcorrect prim_int.
Fail Elpi derive.eqbcorrect prim_float. (* Can not work, we don't have a syntaxtic test *)
Elpi derive.eqbcorrect fo_record.
Elpi derive.eqbcorrect pa_record.
Elpi derive.eqbcorrect pr_record.   
Fail Elpi derive.eqbcorrect dep_record.
Elpi derive.eqbcorrect enum.
Fail Elpi derive.eqbcorrect eq.
Elpi derive.eqbcorrect bool.
Elpi derive.eqbcorrect sigma_bool.
Elpi derive.eqbcorrect sigma_bool2.
Elpi derive.eqbcorrect ord.
Elpi derive.eqbcorrect ord2.
Elpi derive.eqbcorrect val.
Elpi derive.eqbcorrect alias.

End Coverage.

Import Coverage.

Redirect "tmp" Check peano_eqb_correct : forall n m, peano_eqb n m = true -> n = m.
Redirect "tmp" Check peano_eqb_refl : forall n, peano_eqb n n = true.

Redirect "tmp" Check ord_eqb_correct : forall n, eqb_correct (ord_eqb n n).
Redirect "tmp" Check ord_eqb_refl : forall n, eqb_reflexive (ord_eqb n n).

Redirect "tmp" Check ord2_eqb_correct : forall n, eqb_correct (ord2_eqb n n).
Redirect "tmp" Check ord2_eqb_refl : forall n, eqb_reflexive (ord2_eqb n n).

Redirect "tmp" Check val_eqb_correct : eqb_correct val_eqb.
Redirect "tmp" Check val_eqb_refl : eqb_reflexive val_eqb.

Redirect "tmp" Check alias_eqb_correct : eqb_correct alias_eqb.
Redirect "tmp" Check alias_eqb_refl : eqb_reflexive alias_eqb.
