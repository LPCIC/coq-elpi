(* Generates congruence lemmas using reflect

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi.apps.derive Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive Extra Dependency "bcongr.elpi" as bcongr.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

From Coq Require Export Bool.
From elpi Require Export elpi.
From elpi.apps Require Export derive.
From elpi.apps Require Export derive.projK.

Lemma eq_f (T1 : Type) (T2 : Type) (f : T1 -> T2) a b : a = b -> f a = f b.
Proof.
exact (fun h =>
  eq_rect a (fun x => f a = f x) (eq_refl (f a)) b h).
Defined.

Register eq_f as elpi.derive.eq_f.

Elpi Db derive.bcongr.db lp:{{

type bcongr-db constructor -> term -> prop.

:name "bcongr-db:fail"
bcongr-db K _ :-
  M is "derive.bcongr: can't find the boolean congruence for constructor " ^ {std.any->string K},
  stop M.

}}.

(* standalone *)
Elpi Command derive.bcongr.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File injection.
Elpi Accumulate File bcongr.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.bcongr.main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Name is Tname ^ "_bcongr_",
    derive.bcongr.main GR Name _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.bcongr <inductive type name> [<output name suffix>]".
}}.
Elpi Typecheck. 

Elpi Typecheck.
      
(* hook into derive *)
Elpi Accumulate derive Db derive.bcongr.db.
Elpi Accumulate derive File injection.
Elpi Accumulate derive File bcongr.
Elpi Accumulate derive lp:{{
  
dep1 "bcongr" "projK".
derivation (indt T) Prefix (derive "bcongr" (derive.bcongr.main T N)) :- N is Prefix ^ "bcongr_".

}}.
