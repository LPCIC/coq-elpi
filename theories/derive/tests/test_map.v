From elpi Require Import derive.map derive.param1 derive.projK.

Require Vector.
Elpi derive.map list.
Elpi derive.map prod.
Elpi derive.map ex.
Elpi derive.map Vector.t.

Inductive blurb A := K1 (a:A) | K2 (b: list A) (c:blurb A).

Elpi derive.map blurb.

Elpi derive.param1 prod prodR.
Elpi derive.param1 list listR.

Elpi derive.map prodR.

Elpi derive.map listR.
