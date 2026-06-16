Declare ML Module "rocq-elpi-ext.elpi_ext_plugin".

From elpi Require Import elpi.

From elpi.ext Extra Dependency "src.elpi" as src.

Elpi Command C.
Elpi Accumulate File src.

Elpi Query lp:{{
  to_int z N, coq.say N.
}}.