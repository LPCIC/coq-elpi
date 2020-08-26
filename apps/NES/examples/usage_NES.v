From elpi.apps Require Import NES.

(* Namespaces are like modules, since they let you organize your notions
   and avoid name collisions.
   Namespaces are unlinke modules, since you can always add a notion to
   a namespace, even if the namespace was ended before. *)

NES.Begin This.Is.A.Long.Namespace.
  Definition stuff := 1.
NES.End This.Is.A.Long.Namespace.

NES.Begin This.Is.A.Long.Namespace.
  Definition more_stuff := This.Is.A.Long.Namespace.stuff.
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

(* For convenience one can open a namespace to write short names *)
NES.Status.
(*
NES: current namespace []
NES: registered namespaces 
[ns [This] «elpi.apps.NES.examples.usage_NES.This_aux_1.This», 
 ns [This] «elpi.apps.NES.examples.usage_NES.This_aux_2.This», 
 ns [This] «elpi.apps.NES.examples.usage_NES.This_aux_3.This»]
*)
NES.Open This.Is.A.Long.Namespace. (* BUG: does nothing *)
Print stuff. (* BUG: = 2 *)
