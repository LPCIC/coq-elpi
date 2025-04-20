Module lib.
  Definition foo := I.
End lib.
Check lib.foo.                  (* works fine *)
Require Import elpi.elpi.
Check lib.foo.   