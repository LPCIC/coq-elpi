From elpi Require Import elpi.

Require Import List.


(****** typecheck **********************************)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
  coq.typecheck BO TY ok.
}}.

Elpi Query lp:{{
  pi x w z\
    decl x `x` {{ nat }} =>
    def z `z` {{ nat }} x =>
    (coq.say z,
     coq.typecheck z T ok,
     coq.say T,
     coq.say {coq.term->string z},
     coq.say {coq.term->string T}).
}}.

Elpi Query lp:{{
  pi x w z\
    decl x `x` {{ nat }} =>
    decl w `w` {{ nat }} =>
    def z `z` {{ nat }} w =>
    (coq.say z,
     coq.typecheck z T ok,
     coq.say T,
     coq.say {coq.term->string z},
     coq.say {coq.term->string T}).
}}.

Elpi Query lp:{{

  coq.typecheck {{ Prop Prop }} _ (error E),
  coq.say E.

}}.


Elpi Query lp:{{
  coq.unify-leq {{ bool }}  {{ nat }} (error Msg),
  coq.say Msg.
}}.


Elpi Query lp:{{
  coq.locate "cons" GRCons, Cons = global GRCons,
  coq.locate "nil" GRNil, Nil = global GRNil,
  coq.locate "nat" GRNat, Nat = global GRNat,
  coq.locate "O" GRZero, Zero = global GRZero,
  coq.locate "list" GRList, List = global GRList,
  L  = app [ Cons, _, Zero, app [ Nil, _ ]],
  LE = app [ Cons, Nat, Zero, app [ Nil, Nat ]],
  coq.typecheck L (app [ List, Nat ]) ok.
}}.

Definition nat1 := nat.

Elpi Query lp:{{ coq.typecheck {{ 1 }} {{ nat1 }} ok }}.

Definition list1 := list.

Elpi Query lp:{{ coq.typecheck {{ 1 :: nil }} {{ list1 lp:T }} ok, coq.say T }}.

Elpi Query lp:{{ coq.typecheck-ty {{ nat }} (typ U) ok, coq.say U }}.

Elpi Query lp:{{ coq.typecheck-ty {{ nat }} prop (error E), coq.say E }}.

