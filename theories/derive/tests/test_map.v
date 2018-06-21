From elpi Require Import derive.map derive.param1 derive.projK.

From elpi.derive Require Import
  test_derive_stdlib.

Module Coverage.

Elpi derive.map Coverage.empty.
Elpi derive.map Coverage.unit.
Elpi derive.map Coverage.peano.
Elpi derive.map Coverage.option.
Elpi derive.map Coverage.pair.
Elpi derive.map Coverage.seq.
Elpi derive.map Coverage.tree.
Fail Elpi derive.map Coverage.nest.
Fail Elpi derive.map Coverage.w.
Elpi derive.map Coverage.vect.
Elpi derive.map Coverage.dyn.
Fail Elpi derive.map Coverage.zeta.
Fail Elpi derive.map Coverage.beta.
Elpi derive.map Coverage.iota.
Elpi derive.map Coverage.large.

End Coverage.

          

Elpi derive.map nat.

Elpi derive.param1 nat.
Elpi derive.map natR.

Elpi derive.map list.
Elpi derive.param1 list.
Elpi derive.map listR.

Elpi derive.map prod.
Elpi derive.param1 prod.
Elpi derive.map prodR.

Require Vector.
Elpi derive.map Vector.t.

Elpi derive.map ex.

Inductive blurb A := K1 (a:A) | K2 (b: list A) (c:blurb A).

Elpi derive.map blurb.

Inductive dlist A := dnil | dcons (a : A * nat) (l : dlist A).

Elpi derive.map dlist.
Check dlist_map : forall A B, (A -> B) -> dlist A -> dlist B.

Elpi derive.param1 dlist.
Elpi derive.map dlistR.
