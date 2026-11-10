(* Generates congruence lemmas using reflect

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi.apps.derive.elpi Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive.elpi Extra Dependency "bcongr.elpi" as bcongr.
From elpi.apps.derive.elpi Extra Dependency "bcongr.db.elpi" as bcongrdb.
From elpi.apps.derive.elpi Extra Dependency "projK.db.elpi" as projKdb.

From elpi Require Export elpi.
From elpi.apps Require Export derive.
From elpi.apps Require Export derive.projK.

Lemma eq_f (T1 : Type) (T2 : Type) (f : T1 -> T2) a b : a = b -> f a = f b.
Proof.
exact (fun h =>
  eq_rect a (fun x => f a = f x) (eq_refl (f a)) b h).
Defined.

Register eq_f as elpi.derive.eq_f.

Elpi Db derive.bcongr.db lp:{{ accumulate "elpi.apps.derive.elpi/bcongr.db". }}.

(* standalone *)
Elpi Command derive.bcongr.
Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File bcongr.
Elpi Accumulate lp:{{
  main [str I] :- !,
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.bcongr.main GR Prefix _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.bcongr <inductive type name>".
}}.
 


      
(* hook into derive *)
Elpi Accumulate derive Db derive.bcongr.db.
Elpi Accumulate derive File bcongr.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "bcongr" "projK".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "bcongr" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) N ff (derive "bcongr" (derive.bcongr.main T N) (derive.exists-indc T (K\bcongr-db K _))).

}}.
