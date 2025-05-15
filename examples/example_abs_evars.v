From elpi Require Import elpi.

(** Closing a term with holes with binders *)

(*

The operation consists in replacing all occurrences of the same hole
in a term by a bound variable.

We first traverse the term and count how many distinct hole are there
and replace them by a placeholder to be later abstracted.
Once we know how many binders we need, we generate the spine of binders
and replace the placeholders by the bound variables.

This example is interesting because it uses the constraint store
to attach data to holes, in particular if the hole has been seen before,
and to attach to each hole a unique number.

*)

Elpi Tactic abs_evars.
Elpi Accumulate lp:{{

% we add a new constructor to terms to represent terms to be abstracted
type abs int -> term.

% bind back abstracted subterms
pred bind i:int, i:int, i:term, o:term.
bind I M T T1 :- M > I, !,
  T1 = {{ forall x, lp:(B x) }},   
  N is I + 1,
  pi x\                           % we allocate the fresh symbol for (abs M)
    (copy (abs N) x :- !) ==>     % we schedule the replacement (abs M) -> x
    bind N M T (B x).
bind M M T T1 :- copy T T1.         % we perform all the replacements

% for a term with M holes, returns a term with M variables to fill these holes
% the clause see is only generated for a term if it hasn't been seen before
% the term might need to be typechecked first or main generates extra holes for the
% type of the parameters
pred abs-evars i:term, o:term, o:int.
abs-evars T1 T3 M :- std.do! [
  % we put (abs N) in place of each occurrence of the same hole
  ((pi T Ty N N' M \ fold-map T N (abs M) M :- var T, not (seen? T _), !, coq.typecheck T Ty ok, fold-map Ty N _ N', M is N' + 1, seen! T M) ==>
   (pi T N M \ fold-map T N (abs M) N :- var T, seen? T M, !) ==>
     fold-map T1 0 T2 M),
  % we abstract M holes (M abs nodes)
  bind 0 M T2 T3,
  % cleanup constraint store
  purge-seen!,
].

% all constraints are also on _ so that they share
% a variable with the constraint to purge the store

% we query if the hole was seen before, and if so
% we fetch its number
func seen? term, int ->.
seen? X Y :- declare_constraint (seen? X Y) [X,_].  

% we declare it is now seen and label it with a number
func seen! term, int ->.
seen! X Y :- declare_constraint (seen! X Y) [X,_].

% to empty the store
func purge-seen!.
purge-seen! :- declare_constraint purge-seen! [_].

constraint seen? seen! purge-seen!  {
  % a succesful query, give the label back via M
  rule (seen! X N) \ (seen? X M) <=> (M = N).
  % an unsuccesful query
  rule             \ (seen? X _) <=> false.

  rule purge-seen! \ (seen! _ _).
  rule \ purge-seen!.
}

% if we pass an argument this is what we use to refine the goal
solve (goal _ _ _ _ [trm T] as G) GL :-
  std.assert-ok! (coq.elaborate-ty-skeleton T _ T1) "illtyped",
  std.assert! (abs-evars T1 ClosedT1 _) "closure fails",
  refine ClosedT1 G GL.

% if we pass no argument, then we abstract the goal.
% the first subgoal is a proof of the abstracted goal, while
% the other goals are for the abstracted premises
solve (goal _ _ T _ [] as G) GL :-
  std.assert! (abs-evars T ClosedT N) "closure fails",
  coq.mk-app {{ (fun x : lp:ClosedT => x) _ }} {coq.mk-n-holes N} R,
refine R G GL.

}}.

Elpi Export abs_evars.

Fail Lemma test : forall x, x = x.
Lemma test : abs_evars (forall x, x = x).
intros t x; reflexivity.
Abort.

Lemma test : abs_evars (forall x y, x = y).
intros t x y; symmetry.
Abort.

Lemma test : True.
assert (abs_evars (tt = _)) as H.
  intro x; destruct x; reflexivity.
Abort.

Lemma test : exists x, x = tt.
econstructor.
(* it is silly, but shows the code above performs the abstraction *)
elpi abs_evars.
  now intros [].
exact tt.
Qed.
