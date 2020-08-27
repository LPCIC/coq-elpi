From Coq Require Ltac.
Declare ML Module "elpi_plugin".

(* Generate coq-bultins.elpi *)
Elpi Document Builtins.

(* Load once and forall these files in this .vo, to ease redistribution *)
Elpi Checker "elpi/coq-elpi-checker.elpi".
Elpi Printer "elpi2html.elpi".
Elpi Template Command "elpi/elpi-command-template.elpi".
Elpi Template Tactic "elpi/elpi-tactic-template.elpi".

(* Special constant used for HOAS of holes, see coq-bultins.elpi *)
Lemma hole : True. Proof. exact I. Qed.
Register hole as elpi.hole.

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

From Coq Require Floats Int63.

Register Coq.Floats.PrimFloat.float as elpi.float64.
Register Coq.Numbers.Cyclic.Int63.Int63.int as elpi.uint63.
