
From elpi Require Import elpi.
From example_plugin Require Import example_plugin.

Elpi Command test2.
Elpi Accumulate Plugin "elpi_example_plugin.elpi".
Elpi Query lp:{{
  q (stuff 46)
}}.
