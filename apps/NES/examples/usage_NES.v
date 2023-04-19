From elpi.apps Require Import NES.

(* Namespaces are like modules, since they let you organize your notions
   and avoid name collisions.
   Namespaces are unlinke modules, since you can always add a notion to
   a namespace, even if the namespace was ended before. *)

NES.Begin This.Is.A.Long.Namespace.
  Definition stuff := 1.
NES.End This.Is.A.Long.Namespace.

NES.Begin This.Is.A.Long.Namespace.
  Definition more_stuff := stuff. (* stuff in the namespace is visible *)
NES.End This.Is.A.Long.Namespace.

Print This.Is.A.Long.Namespace.stuff. (* = 1 *)
Eval compute in This.Is.A.Long.Namespace.more_stuff. (* = 1 *)

(* Unlike a module, a namespace can contain two notions with the same name.
   The latter shadows the former. *)

NES.Begin This.Is.A.Long.Namespace.
   Definition stuff := 2.
NES.End This.Is.A.Long.Namespace.

(* Binding is static, eg more_stuff still values 1 *)
Print This.Is.A.Long.Namespace.stuff. (* = 2 *)
Eval compute in This.Is.A.Long.Namespace.more_stuff. (* = 1 *)

(* Listing and printing namespaces *)
NES.List This.
(*
This_aux_1.This.Is.A.Long.Namespace.stuff	(* <-- shadowed *)
This.Is.A.Long.Namespace.more_stuff
This.Is.A.Long.Namespace.stuff
*)
NES.Print This.
(*
This_aux_1.This.Is.A.Long.Namespace.stuff : nat
This.Is.A.Long.Namespace.more_stuff : nat
This.Is.A.Long.Namespace.stuff : nat
*)

(* For convenience one can open a namespace to write short names *)
NES.Open This.Is.A.Long.Namespace.
Print stuff.

(* Not quite a name space yet *)
Structure Default := { sort : Type; default : sort }.
NES.Begin CS.
  Global Canonical Structure nat_def := {| sort := nat; default := 46 |}.
  Check @default _ : nat.
NES.End CS.
Fail Check nat_def.
(* we want nat_def to live in the CS namespace, BUT
   we want the canonical structure declaration to live outside the namespace *)
Fail Check @default _ : nat.
(* This behavior requires Libobject to be aware of the role played by
   a module: if it is a namespace some "actions" have to be propagated upward *)
