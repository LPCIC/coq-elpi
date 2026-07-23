(* For each constructor K the function isK returns true iff it is applied
   to K. These helpers are use to implement "discriminate".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "isK.elpi" as isK.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

(* Links the @gref of the constructor K to the isK constant *)
Elpi Db derive.isK.db lp:{{
  func isK-db constructor -> term.
}}.
#[superglobal] Elpi Accumulate derive.isK.db lp:{{

  :name "isK-db:fail"
  isK-db K _ :-
    M is "No isK entry for constructor " ^ {std.any->string K} ^ ". Did you run derive.isK?",
    stop M.

}}.

Elpi Command derive.isK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File isK.
Elpi Accumulate lp:{{
  func derive.isK.standalone-prefix inductive, string, inductive -> string.
  derive.isK.standalone-prefix First Prefix T Prefix :- First = T, !.
  derive.isK.standalone-prefix _ _ T P :- P is {coq.gref->id (indt T)} ^ "_is_".

  func derive.isK.standalone-main inductive, string -> list prop.
  derive.isK.standalone-main T Prefix C :-
    mutual.is-mutual T, !,
    mutual.members T TS,
    std.map TS (t\c\ sigma p\ derive.isK.standalone-prefix T Prefix t p, derive.isK.main t p c) CS,
    std.flatten CS C.
  derive.isK.standalone-main T Prefix C :- derive.isK.main T Prefix C.

  main [str I,str O] :- !, coq.locate I (indt GR), derive.isK.standalone-main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR),
    Prefix is {coq.gref->id (indt GR)} ^ "_is_",
    derive.isK.standalone-main GR Prefix _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.isK <inductive type name> [<output prefix>]".
}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.isK.db.
Elpi Accumulate derive File isK.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "isK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

func derive.isK.derive-main inductive, string -> list prop.
derive.isK.derive-main T Prefix C :- derive.mutual-inductive T, !,
  derive.mutual-inductives T TS,
  std.map TS (t\c\ sigma p n\ mutual.selected-prefix T Prefix t p, n is p ^ "isk_", derive.isK.main t n c) CS,
  std.flatten CS C.
derive.isK.derive-main T Prefix C :- N is Prefix ^ "isk_", derive.isK.main T N C.
  
derivation (indt T) Prefix ff (derive "isK" (derive.isK.derive-main T Prefix) (derive.exists-indc T (K\ isK-db K _))).

}}.
