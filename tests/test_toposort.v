From elpi Require Import elpi.

Elpi Command GraphToposort.

Elpi Query lp:{{
  coq.elpi.toposort [pr "a" ["b"], pr "c" ["a"]] ["c", "a", "b"],
  coq.elpi.toposort [pr 1 [2], pr 3 [1]] [3, 1, 2].
}}.
