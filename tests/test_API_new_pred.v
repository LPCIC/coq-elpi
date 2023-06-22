From elpi Require Import elpi.

Elpi Db search.db lp:{{
  pred p i:int.
  p 1.

  pred unwrap i:list argument, o:list any.
  unwrap [] [].
  unwrap [A | As] [B | Bs] :-
    (A = int B; A = str B; A = trm B),
    unwrap As Bs.
}}.

Elpi Command search.
Elpi Accumulate Db search.db.
Elpi Accumulate lp:{{
  main [str "output", str P | L_args] :-
    unwrap L_args L,
    std.append L [X_] L1,
    coq.elpi.predicate P L1 Q, Q,
    coq.say "I=" {std.last L1}.
  main [str P | L_args] :-
    unwrap L_args L,
    coq.elpi.predicate P L Q, Q.
}}.
Elpi Typecheck.

Elpi Command declare_pred.
Elpi Accumulate lp:{{
  pred mk-arg i:string, o:string.
  mk-arg Ty D :- D is "i:(" ^ Ty ^ ")".
  main [str P|Args] :-
    std.map Args (x\r\x = str r) Args1,
    D is "pred " ^ P ^ " " ^ {std.string.concat "," Args1} ^ ".",
    coq.elpi.add-predicate "search.db" D.
}}.
Elpi Typecheck.

Elpi Command accumulate_pred.
Elpi Accumulate Db search.db.
Elpi Accumulate lp:{{
  main [str P | L] :-
    coq.elpi.predicate P {unwrap L} Q,
    coq.elpi.accumulate _ "search.db" (clause _ _ Q).
}}.
Elpi Typecheck.

Elpi declare_pred "s" "i:int, o:int".
Elpi accumulate_pred "s" 0 3.
Elpi accumulate_pred "s" 0 4.
Elpi search "output" "s" 0.

Elpi search "p" 1.
Fail Elpi search "p" 2.
Elpi accumulate_pred "p" 2.
Elpi search "p" 2.

Elpi declare_pred "q" "i:int".
Fail Elpi search "q" 1.
Elpi accumulate_pred "q" 1.
Elpi search "q" 1.
Fail Elpi search "q".

Elpi declare_pred "r" "o:int".
Elpi accumulate_pred "r" 1.
Elpi search "output" "r".

Elpi declare_pred "tt" "o:term, o:term".
Elpi accumulate_pred "tt" (0) (1).
Elpi search "output" "tt" (0).
Fail Elpi search "output" "tt" (1).
Elpi search "tt" (0) (1).