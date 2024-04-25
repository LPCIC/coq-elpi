From elpi Require Import tc.

Axiom f : (Type -> Type -> Type) -> Type -> Type.
Axiom g : Type -> Type -> Type.

Elpi Accumulate TC.Solver lp:{{
  pred test-max-arity i:(term -> term), i:nat.
  test-max-arity T N :-
    (pi x\ precompile-ho.count-maximal-arity x (T x) M),
    std.assert! (N = M) "[TC] invalid length".
}}.

Elpi Query TC.Solver lp:{{
  test-max-arity (x\ {{lp:x bool}}) (s z),
  test-max-arity (x\ {{f (lp:x bool) (lp:x bool unit nat)}}) (s(s(s z))),
  test-max-arity (x\ {{f (lp:x bool) (lp:x bool unit (lp:x nat))}}) (s(s(s z))),
  test-max-arity (x\ {{forall a c, (forall a b, b (lp:x a) c) -> a lp:x c}}) (s z).
}}.

Elpi Accumulate TC.Solver lp:{{
  pred test-precompile-term i:term, i:term, i:nat.
  test-precompile-term T Exp N' :-
    precompile-ho.precompile-term T T' N,
    std.assert! (Exp = T') "[TC] invalid precompiled term",
    std.assert! (N = N') "[TC] invalid number of maybe-eta". 
}}.

Elpi Query TC.Solver lp:{{
  test-precompile-term {{f g bool}} {{f g bool}} z.
}}.

Elpi Query TC.Solver lp:{{
  test-precompile-term {{forall (x: Type) (y: Type -> Type), False -> f (y x) x}} {{f g bool}} z.
}}.


(* Elpi Query TC.Solver lp:{{
  pi Uva\ sigma X Exp\ is-uvar Uva => (
  X = {{f (fun x y => lp:Uva y x) bool}},
  Exp = app
  [{{f}}, 
    precompile-ho.maybe-eta-tm (fun _ _ x \
      precompile-ho.maybe-eta-tm (fun _ _ y \ app [Uva, y, x]) [Uva, x]) [Uva], 
    {{bool}}],
  test-precompile-term X Exp (s (s z))).
}}.


Elpi Query TC.Solver lp:{{
  pi Uva\ sigma Uva Exp\ is-uvar Uva => (
  X = {{f (fun x y => lp:Uva (lp:Uva y) x) bool}},
  Exp = app
  [{{f}}, 
    precompile-ho.maybe-eta-tm (fun _ _ x \
      precompile-ho.maybe-eta-tm (fun _ _ y \ app [Uva, app[Uva, y], x]) [x]) [], 
    {{bool}}],
  test-precompile-term X Exp (s (s z))).
}}.

Elpi Query TC.Solver lp:{{
  pi Uva\ sigma X Exp\ is-uvar Uva => (
  X = {{f (fun x y => lp:Uva (fun x => lp:Uva y x) x) bool}},
  coq.say "AA",
  Exp = app
  [{{f}}, 
    precompile-ho.maybe-eta-tm (fun _ _ x \
      precompile-ho.maybe-eta-tm (fun _ _ y \ app [Uva, 
      % TODO: replace [y,x] with [y]
        precompile-ho.maybe-eta-tm (fun _ _ z \ app[Uva, y, z]) [y, x], x]) [x]) [], 
    {{bool}}],
  test-precompile-term X Exp (s (s (s z)))).
}}. *)

Elpi Query TC.Solver lp:{{
  pi Uva\

}}. 
