From elpi Require Import elpi.

Elpi Db scoped_db lp:{{
  pred scoped o:string.
}}.

Module LocalAccumulation.
  #[local] Elpi Accumulate scoped_db lp:{{ scoped "local". }}.
  Elpi Query scoped_db lp:{{ scoped "local". }}.
End LocalAccumulation.

Fail Elpi Query scoped_db lp:{{ scoped "local". }}.

Module GlobalAccumulation.
  #[global] Elpi Accumulate scoped_db lp:{{ scoped "global". }}.
End GlobalAccumulation.

Elpi Query scoped_db lp:{{ scoped "global". }}.
