# Writing manual content

This is a reference for people *writing* pages in this manual (the custom
roles and the `.. rocqtop::` directive). For how the manual is built and
deployed, see `../README.md`.

## Roles

All roles below are defined in `_roles_elpi.py`. Every role except `:e:`
links the given name to its declaration in one of `builtin-doc/*.elpi` or
`elpi/*.elpi`, pinned to the last commit that touched that file (resolved
locally via `git log`, not the GitHub API, so the build is deterministic and
offline). If the name isn't found, the build fails (`sphinx-build -W`)
rather than silently producing a dead link.

| Role | Target file | Matches a declaration of... | Name mangling |
|---|---|---|---|
| `:lib:` | `elpi/coq-lib.elpi` | `pred`/`func` | — |
| `:lib-common:` | `elpi/coq-lib-common.elpi` | `pred`/`func` | — |
| `:libred:` | `elpi/elpi-reduction.elpi` | `pred`/`func` | — |
| `:libtac:` | `elpi/elpi-ltac.elpi` | `pred`/`func` | strips a leading `coq.ltac.` |
| `:builtin:` | `builtin-doc/coq-builtin.elpi` | `pred`/`func` | — |
| `:builtin-synterp:` | `builtin-doc/coq-builtin-synterp.elpi` | `pred`/`func` | — |
| `:stdlib:` | `builtin-doc/elpi-builtin.elpi` | `pred`/`func` | strips a leading `std.` |
| `:stdlibfull:` | `builtin-doc/elpi-builtin.elpi` | `pred`/`func` | — |
| `:type:` | `builtin-doc/coq-builtin.elpi` | `data`/`kind`/`typeabbrev`/`symb`/`symbol` | — |
| `:libtype:` | `elpi/coq-lib.elpi` | `data`/`kind`/`typeabbrev`/`symb`/`symbol` | — |
| `:libtype-common:` | `elpi/coq-lib-common.elpi` | `data`/`kind`/`typeabbrev`/`symb`/`symbol` | — |
| `:stdtype:` | `builtin-doc/elpi-builtin.elpi` | `data`/`kind`/`typeabbrev`/`symb`/`symbol` | — |
| `:constructor:` | `builtin-doc/coq-builtin.elpi` | `type`/`symb`/`symbol` | — |
| `:stdconstructor:` | `builtin-doc/elpi-builtin.elpi` | `type`/`symb`/`symbol` | — |
| `:macro:` | `builtin-doc/coq-builtin.elpi` | `macro` | — |
| `:stdlibns:` | `builtin-doc/elpi-builtin.elpi` | `namespace` | — |

`builtin`/`symb` are accepted anywhere `external`/`symbol` is (and vice
versa), so e.g. `:type:` also matches a `builtin data` or `external symb`
declaration.

Examples: `` :builtin:`coq.say` ``, `` :stdlib:`map` `` (declared as
`std.map`), `` :libtac:`fail` `` (declared as `coq.ltac.fail`), ``
:type:`term` ``, `` :constructor:`app` ``.

### `:e:`

`` :e:`...` `` is a plain inline literal, highlighted as Elpi source (no
file lookup, no link) — equivalent to a `` `...` `` with
`:language: elpi`. Use it for any Elpi snippet or identifier that isn't (or
isn't worth) linking, e.g. `` :e:`Proof` ``, `` :e:`c0` ``.

## `.. rocqtop::`

```rst
.. rocqtop:: all
   :name: some-ref
   :assert: evar .* suspended on X0

   Lemma foo : True.
   Elpi blind.
```

Every code sample in this manual runs through a real `rocq top` at build
time via this directive (`_rocqtop_elpi.py`), so what you read is
guaranteed to actually work — a sample that no longer compiles fails the
build (`sphinx-build -W`), it doesn't go silently stale. Each `.rst` file
gets its own `rocq top` process, fed every `.. rocqtop::` block in the file
in document order, so state (definitions, open proofs, `From elpi Require
Import elpi.`, ...) persists across blocks on the same page unless reset.

### Display argument (required, exactly one)

Passed as the directive's argument, e.g. `.. rocqtop:: all`:

| Argument | Shows |
|---|---|
| `all` | both the input sentence(s) and the captured output |
| `in` | only the input |
| `out` | only the captured output |
| `none` | neither — the block still runs (for state/side effects), but renders nothing |

### Flags (optional, space-separated in the same argument)

| Flag | Effect |
|---|---|
| `reset` | sends `Reset Initial.` and re-sends the initial options before this block, blanking all prior state on the page |
| `fail` | the block's sentences are expected to fail: temporarily unsets "exit on error" and automatically also implies `warn` |
| `warn` | temporarily sets `Set Warnings "default"` for this block (restored to `"+default"` afterwards) — e.g. to show a warning without escalating it to a hard error under this manual's stricter default policy |
| `restart` | sends `Restart.` then `Proof.` before the block (restart an in-progress proof) |
| `abort` | sends `Abort All.` after the block |
| `extra-<name>` | the block is expected to fail unless `ROCQRST_EXTRA` (an environment variable set at build time) is `all` or a comma-separated list containing `<name>` — ported from the Rocq manual for gating samples that need an optional dependency; not currently used by any page in this manual |

Example: `.. rocqtop:: all reset` (show everything, start a fresh session
for this block onward).

### `:assert:` (option)

A regex (`re.search`, case-insensitive, `DOTALL`) that must match somewhere
in the block's combined captured output (ANSI codes stripped), or the build
fails with the regex and the actual output in the error message. This is
what replaced the old Alectryon tutorials' hand-written `.. mquote::`
transcripts: instead of prose that can silently drift from what the code
actually prints, the real output is re-checked on every build.

```rst
.. rocqtop:: all
   :assert: evar \(X1 c0\).*suspended on X1, X0

   ...
```

Keep the regex as narrow as it needs to be to pin down the claim you're
making — matching one evar number is usually enough; don't try to assert
the whole output verbatim.

### `:name:` (option)

The standard docutils option: gives the block an explicit target, so it can
be linked to with `:ref:`.

### `ROCQTOP_ARGS` (field, whole-document)

A field list entry (not a directive option) anywhere in the page:

```rst
:ROCQTOP_ARGS: -foo bar
```

passes extra command-line arguments to the `rocq top` process spawned for
that page. Not currently used by any page in this manual.
