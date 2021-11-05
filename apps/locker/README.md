# Locker

The `lock` and `mlock` commands let you lock definitions.

## Example of `lock`

```coq
lock Definition x := 3.
```

is elaborated to

```coq
Lemma x_key_subproof : unit. Proof. exact: tt. Qed.
Definition x := locked_with x_key_subproof 3.
Canonical x_unlock_subterm := Unlock ... (* See SSR rewrite unlock idiom *)
```

Here `locked_with` comes from `ssreflect.v` and protects the body of `x`
under a match on `x_key_subproof` which is `Qed` opaque.
Hence `x` is provably equal to 3, but not computationally equal to it.

Given the canonical structure registration, `rewrite unlock` will replace `x`
by `3`.

## Example of `mlock`

```coq
mlock Definition x := 3.
```

is elaborated to

```coq
Module Type x_Locked.
Axiom body : nat.
Axiom unlock : body = 3.
End x_Locked.
Module x : x_Locked. ... End x.
Notation x := x.body.
Canonical x_unlock_subterm := Unlock x.unlock.
```

Hence `x` (actually `x.body`) is a new symbol and `x.unlock` is its
defining equation.

Given the canonical structure registration, `rewrite unlock` will replace `x`
by `3`.

## Limitations

`mlock` uses a module based locking. The body is really sealed but this
command cannot be used inside sections (since modules cannot be declared
inside sections).

`lock` uses opaque key based locking. It can be used everywhere, even inside
sections, but conversion (term comparison) may cross the lock (by congruence)
and hence compare possibly large terms.

See also the section about locking in [ssereflect.v](https://github.com/coq/coq/blob/master/theories/ssr/ssreflect.v).
