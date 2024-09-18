From elpi.apps.tc.tests Require Import test_coercion.

Include Animals.
Include Bird1.

Elpi Query TC.Solver lp:{{
  true.
}}.
