From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Corelib Require Import PosDef.
From elpi.apps.derive.elpi Extra Dependency "tag.elpi" as tag.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Register positive as elpi.derive.positive.

Local Open Scope positive_scope.

Elpi Db derive.tag.db lp:{{

% this is how one registers the tag function to an inductive and let other
% elpi commands use that piece of info
pred tag-for o:inductive, o:constant.

}}.

(* standalone *)
Elpi Command derive.tag.
Elpi Accumulate Db Header derive.tag.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File tag.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate lp:{{

  func derive.tag.standalone-prefix inductive, string, inductive -> string.
  derive.tag.standalone-prefix First Prefix T Prefix :- First = T, !.
  derive.tag.standalone-prefix _ _ T P :- P is {coq.gref->id (indt T)} ^ "_".

  func derive.tag.standalone-main inductive, string -> list prop.
  derive.tag.standalone-main T Prefix C :-
    coq.env.mutual-inductives T TS, std.length TS N, N > 1, !,
    std.map TS (t\c\ sigma p\ derive.tag.standalone-prefix T Prefix t p, derive.tag.main t p c) CS,
    std.flatten CS C.
  derive.tag.standalone-main T Prefix C :- derive.tag.main T Prefix C.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.tag.standalone-main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.tag <inductive name>".

}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.tag.db.
Elpi Accumulate derive File tag.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "tag" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

func derive.tag.prefix inductive, string, inductive -> string.
derive.tag.prefix First Prefix T Prefix :- First = T, !.
derive.tag.prefix _ _ T P :- P is {coq.gref->id (indt T)} ^ "_".

func derive.tag.derive-main inductive, string -> list prop.
derive.tag.derive-main T Prefix C :- derive.mutual-inductive T, !,
  derive.mutual-inductives T TS,
  std.map TS (t\c\ sigma p\ derive.tag.prefix T Prefix t p, derive.tag.main t p c) CS,
  std.flatten CS C.
derive.tag.derive-main T Prefix C :- derive.tag.main T Prefix C.
  
derivation (indt T) Prefix ff (derive "tag" (derive.tag.derive-main T Prefix) (tag-for T _)).

}}.
