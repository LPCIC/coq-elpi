From elpi Require Import elpi.


Elpi Command test1.
#[synterp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" Group,
    coq.env.begin-module "M" none,
    coq.env.end-module _,
    coq.end-synterp-group Group.
}}.
#[interp] Elpi Accumulate lp:{{
  main [] :-
    coq.replay-synterp-action-group "foo".
}}.
Elpi Typecheck.
Elpi Export test1.

Module test1.
  test1.
End test1.


Elpi Command test2.
#[synterp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" Group,
    coq.env.begin-module "M" none,
    coq.env.end-module _,
    coq.end-synterp-group Group.
}}.
#[interp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" Group,
    coq.env.begin-module "M" none,
    coq.env.end-module _,
    coq.end-synterp-group Group.
}}.
Elpi Typecheck.
Elpi Export test2.

Module test2.
  test2.
End test2.


Elpi Command test3.
#[synterp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" Group_foo,
    coq.begin-synterp-group "bar" Group_bar,
    coq.env.begin-module "M1" none,
    coq.begin-synterp-group "baz" Group_baz,
    coq.env.begin-module "M2" none,
    coq.end-synterp-group Group_baz,
    coq.env.end-module _,
    coq.end-synterp-group Group_bar,
    coq.env.end-module _,
    coq.end-synterp-group Group_foo.
}}.
#[interp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" Group,
    coq.replay-synterp-action-group "bar",
    coq.env.end-module _,
    coq.end-synterp-group Group.
}}.
Elpi Typecheck.
Elpi Export test3.

Module test3.
  test3.
End test3.


Elpi Command test4.
#[synterp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" Group_foo,
    coq.begin-synterp-group "bar" Group_bar,
    coq.env.begin-module "M1" none,
    coq.begin-synterp-group "baz" Group_baz,
    coq.env.begin-module "M2" none,
    coq.end-synterp-group Group_baz,
    coq.env.end-module _,
    coq.end-synterp-group Group_bar,
    coq.env.end-module _,
    coq.end-synterp-group Group_foo.
}}.
#[interp] Elpi Accumulate lp:{{
  main [] :-
    coq.begin-synterp-group "foo" GroupFoo,
    coq.begin-synterp-group "bar" GroupBar,
    coq.replay-next-synterp-actions,
    coq.replay-synterp-action-group "baz",
    coq.replay-next-synterp-actions,
    coq.end-synterp-group GroupBar,
    coq.replay-next-synterp-actions,
    coq.end-synterp-group GroupFoo.
}}.
Elpi Typecheck.
Elpi Export test4.

Module test4.
  test4.
End test4.
