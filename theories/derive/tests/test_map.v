From elpi Require Import derive.map derive.param1 derive.projK.

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

Elpi derive.param1 dlist.

(* Elpi derive.map dlistR. *)