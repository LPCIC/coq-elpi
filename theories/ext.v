Declare ML Module "ext.plug".

From elpi Require Import elpi.

(* loading the src.elpi file declared in the ext_elpi_src library *)
From ext_elpi_src Extra Dependency "src.elpi" as src.

Elpi Command C.
Elpi Accumulate File src.

Elpi Query lp:{{
  to_int z N, coq.say N.
}}.