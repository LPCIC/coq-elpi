From elpi Require Import elpi.


Elpi Command test.program1.
Elpi Accumulate lp:{{
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
Elpi Accumulate lp:{{
  main.
}}.

Fail Elpi Typecheck.

Elpi Command test.att.
Elpi Accumulate lp:{{

  main _ :-
    attributes X,
    coq.say X,
    std.filter X (x\sigma s\ x = attribute s _, (not(rex.match "^elpi\\." s))) A,
    A = [attribute "foo" (leaf-str "bar")| _],
    coq.parse-attributes A [att "foo" string,
                        att "poly" bool,
                        att-ignore-unknown] CL,
    coq.say CL.

}}.
Elpi Typecheck.
#[foo="bar"]
Elpi test.att.

Elpi Export test.att.

#[foo="bar",poly] test.att.
#[foo="bar",poly,suppa(duppa)] test.att.

Elpi Command test.axx.
Elpi Accumulate lp:{{
  main _ :-
    attributes X, 
    std.filter X (x\sigma s\ x = attribute s _, (not(rex.match "^elpi\\." s))) A,
    coq.parse-attributes A [att "foo" attmap] CL,
    CL = [get-option "foo" [get-option "A" "3", get-option "b_2" "yes"]].
}}.
Elpi Typecheck.
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

Elpi Command test_attlabel.
Elpi Accumulate lp:{{
  main _ :-
    attributes A,
    coq.parse-attributes A [
      att "only" attlabel,
      att "foo.x" string,
      att "foo.y" bool,
      ] CL,
    CL = [get-option "elpi.loc" _, get-option "elpi.phase" _,
          get-option "only" [get-option "foo" tt],
          get-option "foo.x" "a",
          get-option "foo.y" ff].
}}.
Elpi Typecheck.
Elpi Export test_attlabel.

#[only(foo(x="a",y=no))] test_attlabel.





