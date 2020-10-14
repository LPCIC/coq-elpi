From elpi Require Import elpi.

(* Define a command to turn records into nested sigma types, suggested
   by M. Maggesi for the UniMath library *)
Elpi Command UM.expand.
Elpi Accumulate lp:{{

% From a record declaration to an iterated sigma type
pred wrap-fields-ty i:record-decl, o:term.
wrap-fields-ty (field _ _ Ty _\ end-record) Ty.
wrap-fields-ty (field _ Proj Ty Fields) {{ sigT lp:F }} :-
  coq.string->name Proj Name,
  F = fun Name Ty Bo,
  pi x\ decl x Name Ty => wrap-fields-ty (Fields x) (Bo x).

% From a record declaration to a function building the iterated pairs
% [wrap-fields-bo Rec Acc SigmaTypeDef SigmaTypeName Builder BuilderType]
%  Builder = fun arg1 .. argn => existT arg1 (existT arg2 (.. argn) ..)
%  Acc gathers arg1 .. argn while building the fun
%  SigmaTypeDef is used to fill in the implicit arguments of existT
%  SigmaTypeName is used for BuilderType = forall arg1 .. argn, SigmaTypeName
pred wrap-fields-bo i:record-decl, i:list term, i:term, i:term, o:term, o:term.
wrap-fields-bo end-record Acc SigTy Sig T Sig :-
  std.rev Acc Args,
  wrap-fields-bo.aux Args SigTy T.
wrap-fields-bo (field _ Proj Ty Fields) Acc SigTy Sig (fun Name Ty Bo) (prod Name Ty Tgt) :-
  coq.string->name Proj Name,
  pi x\ decl x Name Ty => wrap-fields-bo (Fields x) [x|Acc] SigTy Sig (Bo x) (Tgt x).

wrap-fields-bo.aux [Last] _ Last.
wrap-fields-bo.aux [X|XS] {{ sigT lp:F }} {{ existT lp:F lp:X lp:Rest }} :-
  F = fun _ _ G,
  wrap-fields-bo.aux XS (G X) Rest.

% We declare the type and its constructor.
% Missing features:
% - parameters are not supported
% - projections are not synthesized
main [indt-decl (record Name _Sort Kname Fields)] :-
  wrap-fields-ty Fields T,
  std.assert-ok! (coq.typecheck T Ty) "oops, wrap-fields-ty is bugged",
  coq.env.add-const Name T Ty _ C,
  wrap-fields-bo Fields [] T (global (const C) _) K KTy,
  std.assert-ok! (coq.typecheck K KTy) "oops, wrap-fields-bo is bugged",
  coq.env.add-const Kname K KTy _ _.

}}.
Elpi Typecheck.
Elpi Export UM.expand.

(* From now on UM.expand is a regular command taking as the only argument
   a record declaration. *)

UM.expand Record foo := mk_foo {
  f1 : Type;
  f2 : f1 -> Type;
  f3 : forall t : f1, f2 t -> bool
}.

Print foo.
(* foo = {f1 : Type & {f2 : f1 -> Type & forall t : f1, f2 t -> bool}} : Type *)

Print mk_foo.
(* mk_foo = fun (f1 : Type) (f2 : f1 -> Type) (f3 : forall t : f1, f2 t -> bool) =>
              existT (fun f4 : Type => {f5 : f4 -> Type & forall t : f4, f5 t -> bool}) f1
                (existT (fun f4 : f1 -> Type => forall t : f1, f4 t -> bool) f2 f3)
    : forall (f1 : Type) (f2 : f1 -> Type), (forall t : f1, f2 t -> bool) -> foo *)
