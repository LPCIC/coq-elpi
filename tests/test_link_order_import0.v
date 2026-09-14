From elpi Require Import elpi.

Elpi Db foo.db lp:{{
  pred p string, int.

  :name "0"
  p "init" 0.
}}.

Elpi Program bar lp:{{ }}.
Elpi Accumulate Db foo.db.