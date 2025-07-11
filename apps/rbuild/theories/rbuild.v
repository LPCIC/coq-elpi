From elpi.apps.rbuild.elpi Extra Dependency "rbuild.elpi" as rbuild.

From elpi Require Import elpi.
From elpi.apps Require Export coercion.

Inductive unresolved_record :=
  | Stop 
  | More (T : Type) : T -> unresolved_record -> unresolved_record.
Inductive named_field :=
  | Label (S: Type) (T : Type) : (S -> T) -> T -> named_field.

Declare Scope label_scope.
Delimit Scope label_scope with lbl.
Notation " l := v " := (Label _ _ l v)  (at level 99, v at level 98) : label_scope.
Notation "« x ; .. ; y »" :=
  (More _ x%lbl .. (More _ y%lbl Stop) ..  (* stage 1 : field rearranging / padding *)

   :>                                      (* ignition: More .. is not a type *)
   More _ x%lbl .. (More _ y%lbl Stop) ..) (* stage 0 : indtype resolution *)
  (at level 0, x, y at level 100, only parsing).

Notation "« 'unresolved record' »" := (More _ _ _) (at level 0, only printing).

Elpi Accumulate coercion.db File rbuild.

Elpi Accumulate coercion.db lp:{{

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% stage 0: we figure out the inductive type and move to stage 1

% we have labels, we use them to infer the type
coercion _ L {{ unresolved_record }} (sort _) R :-
  rbuild.find-inductive {rbuild.unresolved_record->list L} R, !.

% no labels, we hope the type is imposed by the context
coercion _ _ {{ unresolved_record }} (sort _) R :-
  R = {{ unresolved_record }}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% stage 1: we find the constructor from the type and we apply it
coercion _ L {{ unresolved_record }} Ty R :- rbuild.find-constructor Ty K PL, !,
  rbuild.unresolved_record->list L Args,
  rbuild.reorder PL Args [] SortedArgs,
  coq.mk-app K SortedArgs Candidate,
  std.assert-ok! (coq.typecheck Candidate Ty) "Illtyped record",
  R = Candidate.
  % this type checks R again, maybe we can do as in refine to avoid that

}}.
