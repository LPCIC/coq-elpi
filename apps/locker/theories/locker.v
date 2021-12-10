(* Locking mechanisms.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.locker Extra Dependency "locker.elpi" as locker.

From Coq Require Import ssreflect.
From elpi Require Import elpi.

(** [lock] locks a definition on an opaque key

  + can be used everywhere
  - conversion may cross the lock (by congruence), while reduction will not

  Example:

[[
lock Definition foo : T := bo.
]]

  Synthesizes:
  - [foo_key_subproof] an opaque term of type unit
  - [foo] unfolds to [locked_with foo_key_subproof bo]
  - [Canonical foo_unlock_subterm := Unlockable ...] so that [rewrite unlock]
    exposes the real body

  Supported attributes:
  - [#[key]] lets one override the name of the key

*)

Elpi Command lock.
Elpi Accumulate File locker.
Elpi Accumulate lp:{{
  main [const-decl ID (some Bo) Ty] :- !,
    attributes A,
    coq.parse-attributes A [
      att "key" string,
    ] Opts, !,
    Opts => locker.key-lock ID Bo Ty none.
  main [upoly-const-decl ID (some Bo) Ty UnivDecl] :- !,
    attributes A,
    coq.parse-attributes A [
      att "key" string,
    ] Opts, !,
    Opts => locker.key-lock ID Bo Ty (some UnivDecl).
  main _ :- coq.error "Usage: lock Definition ...".
}}.
Elpi Typecheck.
Elpi Export lock.

(** [mlock] locks a definition behind a module type

  + hard locking (the body is really sealed) 
  - cannot be used inside sections

  Example:

[[
mlock Definition foo : T := bo.
]]

  Synthesizes:
  - [Module Type foo_Locked] with fields [body] and [unlock] where
    [body : T] and [unlock : body = bo]
  - [Module foo : foo_Locked]
  - [foo] a notation for [foo.body]
  - [Canonical foo_unlock_subterm := Unlockable ...] so that [rewrite unlock]
    exposes the real body

*)

Elpi Command mlock.
Elpi Accumulate File locker.
Elpi Accumulate lp:{{
  main [const-decl ID (some Bo) Ty] :- !, locker.module-lock ID Bo Ty none.
  main [upoly-const-decl ID (some Bo) Ty UD] :- !, locker.module-lock ID Bo Ty (some UD).
  main _ :- coq.error "Usage: mlock Definition ...".
}}.
Elpi Typecheck.
Elpi Export mlock.
