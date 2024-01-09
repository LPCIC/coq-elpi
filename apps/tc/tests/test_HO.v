From elpi Require Import tc.

Set TC NameShortPath.

Module FO_app.

Class nice_predicate {T : Type} (P : T -> Prop).

Lemma partial_app: forall (T : Type) (P : T -> T -> Prop), forall x, nice_predicate (P x). intros. split. Qed.

Elpi Accumulate TC.Solver lp:{{

% Since (P X) would be too HO for elpi (not pattern fragment), we use the FO approximation
tc-nice_predicate T (app L) {{ @partial_app lp:T lp:P lp:X }} :-
  unify-FO L 1 P [X].

% Since (P x) has type (prod _ _ _) we also want to support eta for the class
tc-nice_predicate T (fun _ _ _ as F) S :-
  coq.reduction.eta-contract F G, not (F == G), tc-nice_predicate T G S.

}}.
Elpi Typecheck TC.Solver.
 

Lemma ex1 (T : Type) (p : nat -> T -> T -> Prop) (x : T) : nice_predicate (p 0 x).
  apply _.
Defined.
Check eq_refl : ex1 = fun T p x => @partial_app T (p 0) x.

Lemma ex2 (T : Type) (p : nat -> T -> T -> Prop) y : nice_predicate (fun x => p 0 y x).
  apply _.
Defined.
Check eq_refl : ex2 = fun T p y => @partial_app T (p 0) y.

Existing Instance partial_app.
Elpi Override TC TC.Solver None.


Lemma ex3 (T : Type) (p : nat -> T -> T -> Prop) y : nice_predicate (fun x => p 0 x y).
  Fail apply _. (* Coq KO *)
  Fail apply partial_app. (* Coq KO *)
  apply (@partial_app T (fun a b => p 0 b a) y).
Abort.

Lemma ex4 (T : Type) (p : nat -> T -> T -> Prop) y : nice_predicate (fun x => p 0 y x).
  Fail apply _. (* Coq KO *)
  Succeed apply partial_app. (* Coq eta! *)
  apply (@partial_app T (p 0) y).
Abort.

(*
  Elpi Accumulate TC.AddInstances lp:{{
    pred doo.
    pred mem-arity o:term, o:term, o:int.

    pred get_ty_arity i:term, i:term, i:term, o:prop.
    get_ty_arity Ty Var New (mem-arity Var New N) :- coq.count-prods Ty N, not (N = 0).

    :before "1"
    compile-aux (prod N T F) I RevPremises ListVar IsPositive Clause :-
      (if (IsPositive = tt) (Clause = pi x y\ C x y) (Clause = (pi x\ decl x N T => C x y))),
      pi p zz\ sigma NewPremise TC L MemArity\
        get_ty_arity T p zz MemArity, !,
        MemArity => (
          (doo => if (get-TC-of-inst-type T TC, coq.TC.class? TC /*, not (occurs p (F p))*/)
          (compile-aux T p [] [] {neg IsPositive} NewPremise,
            (L = [NewPremise | RevPremises])) (L = RevPremises)),
        compile-aux (F p) I L [p | ListVar] IsPositive (C p zz)).
    :before "1"
    compile-aux (prod N T F) I RevPremises ListVar IsPositive Clause :- !,
      (if (IsPositive = tt) (Clause = pi x\ C x) (Clause = (pi x\ decl x N T => C x))),
      pi p\ sigma NewPremise TC L\
        (if (get-TC-of-inst-type T TC, coq.TC.class? TC /*, not (occurs p (F p))*/)
          (doo => compile-aux T p [] [] {neg IsPositive} NewPremise,
            (L = [NewPremise | RevPremises])) (L = RevPremises),
        compile-aux (F p) I L [p | ListVar] IsPositive (C p)).

    pred copy-ty i:list prop, i:term, o:term, o:list prop.
    copy-ty [] T T1 [] :- copy T T1.
    copy-ty [(mem-arity OLD NEW ARITY)|TL] T T1 [split-app1 NEW OLD X|L] :-
      % (pi A B\ copy (prod A B (x\ app [OLD, x])) (prod A B (x\ NEW x)) :- coq.error "STOP") =>
      (copy (app [OLD|X]) NEW) => copy-ty TL T T1 L.

    :before "1"
    compile-aux Ty I RevPremises ListVar _ Clause :- !,
      std.rev RevPremises Premises,
      coq.mk-app I {std.rev ListVar} AppInst,
      std.findall (mem-arity _ _ _) Mem,
      if (not doo) (
          std.findall (mem-arity _ _ _) L,
          copy-ty L Ty Ty' Prem',
          std.append Prem' Premises Premises'
      ) (Ty = Ty', Premises' = Premises),
      make-tc Ty' AppInst Premises' Clause.
    :after "0"
    add-tc-db _ _ C :- coq.say C, fail.
  }}.
  Elpi Query TC.Solver lp:{{
    3 = 3.
  }}.

*)

Elpi Override TC TC.Solver All.

End FO_app.

(************************************************************************)

Module HO_PF.

Class Extensionality (T : Type).

Lemma fun_1 (A1 : Type) (A2 : A1 -> Type) : Extensionality (forall a : A1, A2 a). split. Qed.

Elpi Accumulate TC.Solver lp:{{

% Since app[A2, a] is in the pattern fragment we rephrase it
% as (A2_PF a) and A2 = {{ fun x => lp:(A2_PF x) }} and then
% eta contract
tc-Extensionality (prod _ A1 a\ A2_PF a) {{ @fun_1 lp:A1 lp:A2 }} :-
  coq.reduction.eta-contract {{ fun a : lp:A1 => lp:(A2_PF a) }} A2.

% this simple version would work for odd, but not for the x = x + 1 example.
% in the lucky case of odd, we would not need the eta contraction
tc-Extensionality (prod _ A1 a\ app [A2, a]) {{ @fun_1 lp:A1 lp:A2 }}.
% this is the version which is easy to explain but in the odd case
% generates an ugly expansion
tc-Extensionality (prod _ A1 a\ A2_PF a) {{ @fun_1 lp:A1 lp:A2 }} :-
  A2 = {{ fun a : lp:A1 => lp:(A2_PF a) }}.

}}.
Elpi Typecheck TC.Solver.

Lemma ex1 : Extensionality (nat -> nat). apply _. Defined.
Check eq_refl : ex1 = @fun_1 nat (fun _ => nat).

Lemma ex2 : Extensionality (forall x : nat, x = x + 1). apply _. Defined.
Check eq_refl : ex2 = @fun_1 nat (fun a => a = a + 1).

Axiom odd : nat -> Type.

Lemma ex3 : Extensionality (forall x : nat, odd x). apply _. Defined.
Goal ex3 = ex3. unfold ex3. match goal with |- @fun_1 nat odd = _ => idtac end. reflexivity. Abort.

End HO_PF.