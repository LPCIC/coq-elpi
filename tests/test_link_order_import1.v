From elpi.tests Require Import test_link_order_import0.

Elpi Accumulate foo.db lp:{{
  :before "0"
  p "before" 1.

  :after "0"
  p "after" 1.
}}.


Elpi Query bar lp:{{
  coq.elpi.accumulate _ "foo.db" (clause _ (before "0") (p "before" 11)).
}}.

Elpi Query bar lp:{{
  coq.elpi.accumulate _ "foo.db" (clause _ (after "0") (p "after" 11))
}}.