Declare ML Module "rocq-elpi.elpi_example_plugin".

From elpi Require Import elpi.

Elpi Command test.

Fail Elpi Query lp:{{
  q (stuff 46)
}}.

Elpi Accumulate Plugin "elpi_example_plugin.elpi".

Elpi Query lp:{{
  q (stuff 46)
}}.
