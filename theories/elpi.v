(* This should be covered by dynlink *)
From Coq Require Ltac.

(* Legacy can't work here *)
(* Declare ML Module "elpi_plugin:coq-elpi.plugin". *)
Declare ML Module "coq-elpi.plugin".

(* Generate coq-bultins.elpi *)

(* This fails to write in Dune :S *)
(* Elpi Document Builtins. *)

(* Load once and forall these files in this .vo, to ease redistribution *)
Elpi Checker "coq://elpi/coq-elpi-checker.elpi".
Elpi Printer "elpi2html.elpi". (* this one is from elpi *)
Elpi Template Command "coq://elpi/elpi-command-template.elpi".
Elpi Template Tactic "coq://elpi/elpi-tactic-template.elpi".

(* Special constant used for HOAS of holes, see coq-bultins.elpi *)
Lemma hole : True. Proof. exact I. Qed.
Register hole as elpi.hole.

(* Special constant used for HOAS of match over unknown inductive type
   in terms like "let (a,b...) := t in ..." *)
Inductive unknown_inductive : Prop := unknown_constructor.
Register unknown_inductive as elpi.unknown_inductive.

(* Special global constant used to signal a datum of type gref which
   has no corresponding Coq global reference. This typically signals
   an error: a term like (global (const X)) has no meaning in Coq, X must
   be an actual name.
*)
Inductive unknown_gref : Prop := .
Register unknown_gref as elpi.unknown_gref.

(* Common constants available inside Coq's syntax {{ ... lib:<name> ... }} *)
Register Coq.Init.Logic.eq      as elpi.eq.
Register Coq.Init.Logic.eq_refl as elpi.erefl.

Register Coq.Init.Logic.False as elpi.False.

Register Coq.Init.Datatypes.bool  as elpi.bool.
Register Coq.Init.Datatypes.andb  as elpi.andb.
Register Coq.Init.Datatypes.true  as elpi.true.
Register Coq.Init.Datatypes.false as elpi.false.

From Coq Require Bool.

Register Coq.Bool.Bool.reflect  as elpi.reflect.
Register Coq.Bool.Bool.ReflectF as elpi.ReflectF.
Register Coq.Bool.Bool.ReflectT as elpi.ReflectT.

From Coq Require PrimFloat PrimInt63.

Register Coq.Floats.PrimFloat.float as elpi.float64.
Register Coq.Numbers.Cyclic.Int63.PrimInt63.int as elpi.uint63.
