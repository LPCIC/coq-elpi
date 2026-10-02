# Rocq-Elpi reference manual

This directory holds the Sphinx-based reference manual published at
<https://lpcic.github.io/coq-elpi/refman/>.

## Source layout

Only `docs/base/` is tracked by git; everything else under `docs/` is
generated and gitignored.

- `docs/base/conf.py` — Sphinx configuration: registers the custom
  lexers/roles/directive below, sets the theme (`sphinx_rtd_theme`), etc.
- `docs/base/_pygments_elpi.py` — a Pygments lexer for Elpi, and for Rocq
  with embedded `lp:{{ ... }}` Elpi quotations, used both for
  `.. code-block::`/`:e:`-style highlighting and by `_rocqtop_elpi.py` below.
- `docs/base/_roles_elpi.py` — custom roles (`:builtin:`, `:stdlib:`,
  `:type:`, `:lib:`, ...) that link a predicate/type/macro name to its
  declaration in `builtin-doc/*.elpi` or `elpi/*.elpi`, resolved locally via
  `git log` (no network access at build time).
- `docs/base/_rocqtop_elpi.py` — the `.. rocqtop::` directive: spawns a real
  `rocq top` process and feeds it the block's Rocq/Elpi sentences one at a
  time, rendering the sentence together with its *actually captured* output.
  This is what every tutorial/example page uses for its code samples instead
  of static transcripts, so a sample that no longer compiles breaks the
  build rather than silently going stale.
- `docs/base/index.rst`, `getting-started.rst`, `apps.rst`,
  `tutorials/`, `reference/`, `examples/` — the manual's actual content.
- `docs/base/_static/custom.css` — small CSS additions on top of the theme
  (ANSI colors for `.. rocqtop::` output, Elpi-specific token colors, ...).

## Building

```
make refman-build
```

(from the repository root) does, in order:

1. `dune build -p rocq-elpi @install` — builds the `.install` files
   `dune install` (next step) needs; without it, `dune install` fails with
   `<package>.install are missing` unless some earlier, unrelated full
   `dune build` happened to already produce them.
2. `dune build builtin-doc` — `_roles_elpi.py` reads `builtin-doc/*.elpi`
   straight off disk, so it must exist and be up to date.
3. `dune install rocq-elpi` — installs Rocq-Elpi into the current opam
   switch. This is required (not just building it in place) because
   `.. rocqtop::` spawns a real `rocq top` that loads `From elpi Require
   Import elpi.` the same way an end user's opam switch would.
4. Copies `docs/base/` to `docs/source/` (gitignored), substituting
   `@@VERSION@@` in `conf.py` with `git describe --always`.
5. Runs `sphinx-build -q -W -b html docs/source docs/build`. `-W` turns
   every warning into a hard build failure — a broken `:builtin:`/`:doc:`
   reference, a `.. rocqtop::` sentence that errors out, or a dangling
   toctree entry all fail the build rather than degrading quietly.

`docs/source/` and `docs/build/` are both deleted and recreated on every
run; never edit files there by hand.

Requirements beyond the repository's usual opam/dune setup: `Sphinx` and
`sphinx-rtd-theme` (`pip install Sphinx sphinx-rtd-theme`), installed into
whichever Python `sphinx-build` resolves to on `$PATH`.

To build and preview locally:

```
make refman-serve   # builds, then serves docs/build/ on http://localhost:8000
```

## Deployment

`.github/workflows/doc.yml` runs on every push/PR to `master`. On `master`
it builds **two** things and deploys them together to the `gh-pages` branch
(published at <https://lpcic.github.io/coq-elpi/>):

- `make doc` — the older per-tutorial pages rendered with
  [Alectryon](https://github.com/cpitclaudel/alectryon) from
  `examples/tutorial_*.v`, output to `doc/`. These keep their original,
  already-linked-elsewhere paths, e.g.
  `https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html` — every new
  manual tutorial page links back to its Alectryon-rendered original via a
  `.. seealso::` note, so these paths must not move.
- `make refman-build` — this Sphinx manual, output to `docs/build/`, copied
  into the deployed site under `refman/`, i.e.
  `https://lpcic.github.io/coq-elpi/refman/`.

The workflow's `combine docs for deployment` step lays both out under one
`site/` directory (`doc/*` at the root, `docs/build/*` under `site/refman/`)
before handing it to `JamesIves/github-pages-deploy-action`, which force-pushes
`site/` as the full contents of the `gh-pages` branch.
