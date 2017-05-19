From elpi Require Import elpi.

Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-refiner.elpi".

Elpi Run "
  {{plus}} = const GR, coq-env-const GR B T,
  of B TY RB, coq-say RB, coq-say TY".

Elpi Run "
  {{plus_n_O}} = const GR, coq-env-const GR B T,
  of B TY RB, coq-say RB, coq-say TY".