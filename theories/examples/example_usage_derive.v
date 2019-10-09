(**
   This example shows how to use Elpi derive
*)

From elpi Require Import derive.

(** The basic invocation is with just one argument, the inductive
    type name *)
Elpi derive nat.
Check nat_eq_OK. (* generated constants are prefixed with nat_ *) 

(** This is a tricky case *)
Inductive rtree A := Leaf (a : A) | Node (l : list (rtree A)).
(** Indeed the standard eliminator is not very useful *)
About rtree_ind.
(** Let's opt out *)
Unset Elimination Schemes.

(** Elpi derive wants all dependencies to be derived in order,
    so we start with lists.
    
    This time we put all generated constants into a namespace (a module) *)
Module list.
(** The second argumet overrides the default prefix *)
Elpi derive list "".
End list.  

Module rtree.
(** The derivations above also registers in elpi's data bases
    the generated constants. Unless imported these data base
    entries are not visible to elpi. *)
Import list.
Elpi derive rtree "".
End rtree.

Print rtree.eq.        (** Looks ok, and uses list.eq to compare nodes *)
Check rtree.eq_OK.     (** This is the correctness proof *)
Check rtree.induction. (** That's the key... *)
Print rtree.map.       (** Bonus: utility function *)
Print Module rtree.    (** That's all folks *)

