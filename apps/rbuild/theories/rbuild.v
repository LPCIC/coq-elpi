From elpi.apps.rbuild.elpi Extra Dependency "rbuild.elpi" as rbuild.

From elpi Require Import elpi.
From elpi.apps.derive Require Export lens.
From elpi.apps Require Export coercion.
Require ssr.ssrfun.

Inductive unresolved_record :=
  | Stop 
  | More (T : Type) : T -> unresolved_record -> unresolved_record.
Inductive named_field (S: Type) :=
  | Label (T : Type) : (S -> T) -> T -> named_field.

Declare Scope label_scope.
Delimit Scope label_scope with lbl.
Declare Scope labeled_scope.
Delimit Scope labeled_scope with lbled.
Notation " a # b" := (ssrfun.catcomp a b) (at level 0, b at level 0) : label_scope.
Notation " l := v " := (Label _ _ l%lbl v)  (at level 51, v at level 98) : labeled_scope.
Notation "« x ; .. ; y »" :=
  (More _ x%lbled .. (More _ y%lbled Stop) ..  (* stage 1 : field rearranging / padding *)

   :>                                      (* ignition: More .. is not a type *)
   More _ x%lbled .. (More _ y%lbled Stop) ..) (* stage 0 : indtype resolution *)
  (at level 0, x, y at level 100, only parsing).

Notation "« 'unresolved record' »" := (More _ _ _) (at level 0, only printing).

Inductive update := With (T : Type) : T -> named_field T -> update.

Notation "« x 'with' l := v »" := (With _ x (Label _ _ l%lbl v) : With _ x (Label _ _ l%lbl v))
  (at level 0, x at level 100, l at level 0, v at level 98, only parsing).


Elpi Accumulate coercion Db derive.lens.db.

Elpi Accumulate coercion File rbuild.


Elpi Accumulate coercion.db lp:{{

% workaround: this should work: Elpi Accumulate coercion.db File Signature rbuild.
func rbuild.find-inductive list term -> term.
func rbuild.reorder list (option constant), list term, list term -> list term.
func rbuild.unresolved_record->list term -> list term.
func rbuild.focus term, list constant -> term.
func rbuild.find-constructor term -> term, list (option constant).

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

% stage 0, we schedule the update for stage 1
coercion _ {{ With lp:R _ _}} {{ update }} (sort _) R.

% stage 1, we update X via a lens on L
coercion _ {{ With lp:R lp:X (Label _ _ lp:L lp:V )}} {{ update }} R O :- std.do! [
  rbuild.focus L [] Focus,
  Candidate = {{ over lp:Focus (fun _ => lp:V) lp:X }},
  std.assert-ok! (coq.typecheck Candidate R) "illtyped update",
  O = Candidate,
].

}}.
