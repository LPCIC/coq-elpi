From elpi.apps Require Import NES.

NES.Begin A.
  Definition cats := 3.
NES.End A.

NES.Begin B.
  Definition dogs := 4.
NES.End B.

NES.Begin C.

  NES.Begin A.
    Definition bunnies := 42.
  NES.End A.

  Section more_bunnies.
    NES.Open A.
    Definition more_bunnies := bunnies.
  End more_bunnies.

  Section more_cats.
    NES.Open _.A.
    Definition more_cats := cats.
  End more_cats.

  Section more_dogs.
    NES.Open B.
    Definition more_dogs := dogs.
  End more_dogs.

  Section even_more_dogs.
    NES.Open _.B.
    Definition even_more_dogs := dogs.
  End even_more_dogs.

NES.End C.
