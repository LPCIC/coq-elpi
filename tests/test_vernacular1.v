From elpi Require Import elpi.


Elpi Command test.program1.
Elpi Accumulate lp:{{
  pred foo i:list argument.
  main X :- coq.say "test1", foo X.
}}.

Elpi Command test.program2.
Elpi Accumulate lp:{{
  main _ :- coq.say "test2".
}}.

Elpi Accumulate test.program1 lp:{{
  foo [S] :- coq.say S.
  foo [X,Y] :- coq.say X, coq.say Y.
  foo _ :- coq.say "too many arguments".
}}.

Elpi test.program2.
Elpi test.program1 "hello".
Elpi test.program1 "hello" -my.
Elpi test.program1 "hello my" Dear.
Elpi test.program1 "hello" too many args.

Elpi Command test.program3.
Fail Elpi Accumulate lp:{{
  main.
}}.
(* Fail  *)

Elpi Command test.att.
Elpi Accumulate lp:{{

  main _ :-
    attributes A,
    coq.say A,
    A = [attribute "elpi.loc" _, attribute "elpi.phase" _, attribute "foo" (leaf-str "bar")| _],
    coq.parse-attributes A [att "foo" string,
                        att "poly" bool,
                        att-ignore-unknown] CL,
    coq.say CL.

}}.

#[foo="bar"]
Elpi test.att.

Elpi Export test.att.

#[foo="bar",poly] test.att.
#[foo="bar",poly,suppa(duppa)] test.att.

Elpi Command test.axx.
Elpi Accumulate lp:{{
  main _ :-
    attributes A, coq.parse-attributes A [att "foo" attmap] CL,
    CL = [get-option "elpi.loc" _, get-option "elpi.phase" _, get-option "foo" [get-option "A" "3", get-option "b_2" "yes"]].
}}.

Elpi Export test.axx.

#[foo(A="3", b_2="yes")] test.axx.

Elpi Query test.att lp:{{ X = 3 }}.

Elpi Command test.scope.
Elpi Accumulate lp:{{
  main [trm X, str"%", str Id] :- coq.say X Id.
  main L :- coq.error L.
}}.
Elpi test.scope (_ * _)%type.
Fail Elpi test.scope ((_ * _)%type).
