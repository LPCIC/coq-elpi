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
  func derive.projK.standalone-prefix inductive, string, inductive -> string.
  derive.projK.standalone-prefix First Prefix T Prefix :- First = T, !.
  derive.projK.standalone-prefix _ _ T P :- P is {coq.gref->id (indt T)} ^ "_getk_".

  func derive.projK.standalone-main inductive, string -> list prop.
  derive.projK.standalone-main T Prefix C :-
    mutual.is-mutual T, !,
    mutual.members T TS,
    std.map TS (t\c\ sigma p\ derive.projK.standalone-prefix T Prefix t p, derive.projK.main t p c) CS,
    std.flatten CS C.
  derive.projK.standalone-main T Prefix C :- derive.projK.main T Prefix C.

  main [str I, str O] :- !, coq.locate I (indt GR), derive.projK.standalone-main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.projK.standalone-main GR "proj" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.projK <inductive type name> [<output prefix>]".
}}.



(* hook into derive *)
Elpi Accumulate derive Db derive.projK.db.
Elpi Accumulate derive File projK.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "projK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

func derive.projK.derive-main inductive, string -> list prop.
derive.projK.derive-main T Prefix C :- derive.mutual-inductive T, !,
  derive.mutual-inductives T TS,
  std.map TS (t\c\ sigma p n\ mutual.selected-prefix T Prefix t p, n is p ^ "getk_", derive.projK.main t n c) CS,
  std.flatten CS C.
derive.projK.derive-main T Prefix C :- N is Prefix ^ "getk_", derive.projK.main T N C.
  
derivation (indt T) Prefix ff (derive "projK" (derive.projK.derive-main T Prefix) (derive.exists-indc T (K\ projK-db K _ _))).

}}.
