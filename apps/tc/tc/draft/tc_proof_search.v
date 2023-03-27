Class inhab A := { def : A }.

#[local] Instance nat_inhab : inhab nat := { def := 3 }.
#[local] Instance bool_inhab : inhab bool := { def := false }.
#[local] Instance pair_inhab A B `{inhab A, inhab B} : inhab (A * B)%type := { def := (def,def) }.

Print pair_inhab.

Axiom P : forall (T : Type), forall x:  T, Prop.
Arguments P {_} _.
Axiom xxx : False.
Lemma toto (T : Type) (_ : inhab T) : forall (x : T), P x.
elim xxx.
Qed.


Definition titi : P (3,false) := 
  @toto _ _ _.

(* apply toto. *)
Set Typeclasses Debug.
Lemma aaa: P (3, false).
apply (@toto _ _ _).
(* apply (@toto (nat * bool) _ (3,false)). *)
Qed.
