From elpi Require Import elpi test_vernacular1.

Elpi test.program1 "hello" x.
Elpi test.program1 "hello" x y.

#[fwd_compat_attr] Elpi Command foo.
#[fwd_compat_attr] Elpi Accumulate " main _ :- coq.say {attributes}. ".
#[fwd_compat_attr] Elpi Export foo.
#[fwd_compat_attr] Elpi Query lp:{{ true }}.
#[fwd_compat_attr] Elpi foo.
#[fwd_compat_attr] foo.

(* reentrance *)

Elpi Command the_command.
Elpi Accumulate lp:{{
  pred mk-lem i:string.
  mk-lem Name :- std.do! [
    Lem = {{ (1 + 1 = 2)%nat }},
    std.assert-ok! (coq.elaborate-skeleton Lem _ ELem) "failed",
    std.assert-ok! (coq.typecheck {{ lp:Bo : lp:ELem }} _) "failed",
    coq.ltac.collect-goals Bo [SealedGoal] [],
    coq.ltac.open (coq.ltac.call "ltac1_that_calls_elpi" []) SealedGoal [],
    % !tactic_mode should equal false here
    coq.env.add-const Name Bo ELem @transparent! C_,
  ].

  main [str Name] :- std.do! [
    mk-lem Name
  ].
}}.

Elpi Export the_command.

Elpi Tactic elpi_tac.
Elpi Accumulate lp:{{
  solve (goal _Ctx _ {{ (1 + 1 = lp:EX)%nat }} _ _) _ :- std.do! [
    X = {{ 2%nat }},
    std.assert-ok! (coq.elaborate-skeleton X _ EX) "failed",
  ].
  solve _ _ :- coq.ltac.fail _ "failed".
}}.


Ltac ltac1_that_calls_elpi :=
  elpi elpi_tac;
  reflexivity.

the_command xx.
