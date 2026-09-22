From elpi Require Import elpi.

Elpi Command cmd.

#[synterp]
Elpi Accumulate cmd lp:{{
  main _ :-
    coq.env.begin-section "S",
    coq.env.end-section.
}}.

Set Printing Universes.
#[universes(polymorphic)]
Inductive PolyEmpty@{u} : Type@{u} :=.

#[universes(polymorphic=no)]
Inductive MonoEmpty@{u} : Type@{u} :=.

Elpi Accumulate lp:{{
  main _ :-
    coq.env.begin-section "S",
    coq.univ.add-section "v" U,
    coq.univ.variable U UV,
    coq.univ-instance UI [UV],
    Ty = sort (typ U),
    [@keepunivs!, @keep-alg-univs!] ==>
    coq.env.add-section-variable "T1" _ Ty CT1,
    T1 = global (const CT1),
    coq.env.add-section-variable "T2" _ Ty CT2,
    T2 = global (const CT2),
    (@uinstance! UI => coq.env.global {{:gref PolyEmpty}} PolyEmpty),
    coq.env.add-section-variable "PE" _ PolyEmpty _,
    coq.env.global {{:gref MonoEmpty}} MonoEmpty,
    coq.env.add-section-variable "ME" _ MonoEmpty _,
    std.assert-ok! (coq.elaborate-skeleton {{ lp:T1 -> lp:T2 -> lp:PolyEmpty -> lp:MonoEmpty -> lp:Ty }} _ FBo) "",
    (@udecl! [] tt [] ff => coq.env.add-const "F" FBo _ @transparent! _),
    coq.env.end-section.
}}.

Elpi cmd.

Fail Elpi Query "coq.univ.add-section U".
(* No open section *)

Set Printing Universes.
Print F.
(*
  F@{v} =
  fun T1 T2 : Type@{v} => T1 -> T2 -> PolyEmpty@{v} -> MonoEmpty -> Type@{v}
      : Type@{v} -> Type@{v} -> Type@{max(MonoEmpty.u,v+1)}
  (* v |=  *)
*)
