From elpi Require Import test_vernacular1.

Elpi test.program1 "hello" x.
Elpi test.program1 "hello" x y.

#[fwd_compat_attr] Elpi Command foo.
#[fwd_compat_attr] Elpi Accumulate " main _ :- coq.say {attributes}. ".
#[fwd_compat_attr] Elpi Typecheck.
#[fwd_compat_attr] Elpi Export foo.
#[fwd_compat_attr] Elpi Query lp:{{ true }}.
#[fwd_compat_attr] Elpi foo.
#[fwd_compat_attr] foo.