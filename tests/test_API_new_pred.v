From elpi Require Import elpi.

Elpi Db search.db lp:{{

pred p i:int.
p 1.

}}.

Elpi Command search.
Elpi Accumulate Db search.db.
Elpi Accumulate lp:{{
main [str P, int I] :-
  coq.elpi.predicate P [I] Q,
  Q.
main [str P] :-
  coq.elpi.predicate P [I_] Q,
  coq.say "Query" Q,
  Q,
  coq.say "Result" Q.
}}.


Elpi Command declare_pred.
Elpi Accumulate lp:{{

pred make-args i:list argument, o:list (pair argument_mode string).
make-args [] [].
make-args [str"i",str T|A] [pr in T|L] :- make-args A L.
make-args [str"o",str T|A] [pr out T|L] :- make-args A L.
  
main [str P|Args] :-
  make-args Args Spec,
  coq.elpi.add-predicate "search.db" _ P Spec.
}}.


Elpi Command accumulate_pred.
Elpi Accumulate Db search.db.
Elpi Accumulate lp:{{
main [str P,int I] :-
  coq.elpi.predicate P [I] Q,
  coq.elpi.accumulate _ "search.db" (clause _ _ Q).
}}.


Elpi search "p" 1.
Fail Elpi search "p" 2.
Elpi accumulate_pred "p" 2.
Elpi search "p" 2.

Elpi declare_pred "q" "i" "int".
Fail Elpi search "q" 1.
Elpi accumulate_pred "q" 1.
Elpi search "q" 1.
Fail Elpi search "q".

Elpi declare_pred "r" "o" "int".
Elpi accumulate_pred "r" 1.
Elpi search "r".
