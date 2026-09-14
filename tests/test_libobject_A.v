From elpi Require Import elpi.

#[interp] Elpi Db a.db lp:{{
  pred a -> term.
  :name "init" a {{ 0 }}.
  a {{ 1 }}.
}}.
