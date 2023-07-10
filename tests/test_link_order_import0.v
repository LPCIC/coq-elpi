From elpi Require Import elpi.

Elpi Db foo.db lp:{{
  pred p i:string, i:int.

  :name "0"
  p "init" 0.
}}.

Elpi Program bar lp:{{ }}.
Elpi Accumulate Db foo.db.