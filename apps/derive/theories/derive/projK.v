(* Generates a projection for each argument of each constructor.

   The projection is expected to be applied to an explicit construcor and all
   its arguments. It is used to implement "injection".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "projK.elpi" as projK.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

Elpi Db derive.projK.db lp:{{
func projK-db constructor -> int, term.
}}.
#[superglobal] Elpi Accumulate derive.projK.db lp:{{

:name "projK-db:fail"
projK-db GR N _ :-
  M is "derive.projK: can't find the projection " ^ {std.any->string N} ^ " for constructor " ^ {std.any->string GR},
  stop M.

}}.

Elpi Command derive.projK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File projK.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.projK.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.projK.main GR "proj" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.projK <inductive type name> [<output prefix>]".
}}.



(* hook into derive *)
Elpi Accumulate derive File projK.
Elpi Accumulate derive Db derive.projK.db.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "projK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) Prefix ff (derive "projK" (derive.projK.main T N) (derive.exists-indc T (K\ projK-db K _ _))) :- N is Prefix ^ "getk_".

}}.
