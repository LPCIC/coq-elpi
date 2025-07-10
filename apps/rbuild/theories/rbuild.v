From elpi.apps.rbuild.elpi Extra Dependency "rbuild.elpi" as rbuild.

From elpi Require Import elpi.
From elpi.apps Require Export coercion.

Inductive nulist := Stop | More (T : Type) : T -> nulist -> nulist.
Inductive lfield := Label (S: Type) (T : Type) : (S -> T) -> T -> lfield.

Declare Scope label_scope.
Delimit Scope label_scope with lbl.
Notation " l := v " := (Label _ _ l v)  (at level 0) : label_scope.
Notation "« x ; .. ; y »" := (More _ x%lbl .. (More _ y%lbl Stop) ..) (at level 0).

Elpi Accumulate coercion.db File rbuild.

Elpi Accumulate coercion.db lp:{{

coercion _ L {{ nulist }} Ty R :- std.spy-do! [
  not (var Ty),
  coq.safe-dest-app Ty Hd _,
  coq.env.global (indt I) Hd,
  coq.env.indt I _ _ _ _ [K] _,
  coq.env.projections I PL,
  rbuild.nulist->list L Args,
  rbuild.reorder PL Args SortedArgs,
  coq.mk-app {coq.env.global (indc K)} SortedArgs R,
].

}}.

