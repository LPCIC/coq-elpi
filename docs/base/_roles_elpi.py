"""
Custom Sphinx roles that link an Elpi predicate/type/macro/namespace name to
its declaration, inside one of coq-elpi's own generated/hand-written ``.elpi``
files, on GitHub.

Modelled on elpi's own ``docs/base/_roles_elpi.py`` (a single ``:stdlib:``
role resolved locally via ``git``, no network calls at build time), but
generalized from that module's single hardcoded ``(file, pattern)`` pair into
a table of role specifications, one per role, reproducing every role
previously declared in ``etc/tutorial_style.rst`` (there built on top of a
``ghref`` role in ``etc/alectryon_elpi.py`` that resolved links by querying
the *live* GitHub API at build time).

Unlike that ``ghref`` role, this module never touches the network: every
target file (``builtin-doc/*.elpi``, ``elpi/*.elpi``) is a file of *this*
repository, read straight off disk, and the commit each link points at is
resolved with a local ``git log`` call rather than the GitHub API. This makes
the manual's build deterministic and offline, at the cost of the link being
pinned to the last commit that touched the target file (so it stays a stable
permalink even as that file is edited on ``master`` after a given manual is
published) rather than to whatever the live default branch currently is.
"""

import os
import re
import subprocess
from dataclasses import dataclass
from functools import lru_cache
from string import Template
from typing import Optional, Tuple

from docutils import nodes
from docutils.parsers.rst import roles

REPO_ORG = "LPCIC"
REPO_NAME = "coq-elpi"

_HERE = os.path.dirname(os.path.abspath(__file__))


def _git(cwd, *args):
    return subprocess.run(
        ['git', *args], cwd=cwd, capture_output=True, text=True, check=True,
    ).stdout


@lru_cache(maxsize=1)
def _repo_root():
    # Resolved from _HERE (this file's own directory), which is inside the
    # working tree whether this module runs from docs/base or from its
    # doc-build copy docs/source. Every other git/file call below is then
    # relative to root, so target_path (repo-root-relative) resolves
    # correctly regardless of where this module itself happens to live.
    return _git(_HERE, 'rev-parse', '--show-toplevel').strip()


@lru_cache(maxsize=None)
def _pin(target_path):
    """(full_sha, source_lines) for target_path: full_sha is the commit to
    link against (the last one that touched the file), source_lines is the
    file's current on-disk content, split into lines, used for the per-role
    linear search below."""
    root = _repo_root()
    target = os.path.join(root, target_path)

    full_sha = _git(root, 'log', '-1', '--format=%H', '--', target_path).strip()
    if not full_sha:
        raise RuntimeError(f"{target_path} has no git history")

    with open(target, encoding='utf-8') as f:
        source = f.read()

    return full_sha, source.splitlines()


# -- Pattern families ---------------------------------------------------
#
# Lifted verbatim (as $name-templated strings, per string.Template) from the
# `:pattern:` values already used by the various `ghref`-based roles in
# etc/tutorial_style.rst.

PRED_FUNC_PATTERN = (
    r"^(% \[$name|(external )?(pred|func) $name|(builtin )?(pred|func) $name)"
)
TYPE_PATTERN = (
    r"^((builtin )?data $name|kind $name|typeabbrev $name|"
    r"(external )?symb(ol)? $name|(builtin )?symb(ol)? $name)"
)
CONSTRUCTOR_PATTERN = (
    r"^(type $name|(external )?symb(ol)? $name|(builtin )?symb(ol)? $name)"
)
MACRO_PATTERN = r"^macro $name"
NAMESPACE_PATTERN = r"^namespace $name"


@dataclass(frozen=True)
class RoleSpec:
    name: str
    target_path: str  # repo-root-relative
    pattern: str  # $name-templated regex, per string.Template
    mangle: Optional[Tuple[str, str]] = None  # (re.sub pattern, replacement)


ROLE_TABLE = [
    RoleSpec("lib", "elpi/coq-lib.elpi", PRED_FUNC_PATTERN),
    RoleSpec("lib-common", "elpi/coq-lib-common.elpi", PRED_FUNC_PATTERN),
    RoleSpec("libred", "elpi/elpi-reduction.elpi", PRED_FUNC_PATTERN),
    RoleSpec("libtac", "elpi/elpi-ltac.elpi", PRED_FUNC_PATTERN,
             mangle=(r"^coq\.ltac\.", "")),
    RoleSpec("builtin", "builtin-doc/coq-builtin.elpi", PRED_FUNC_PATTERN),
    RoleSpec("builtin-synterp", "builtin-doc/coq-builtin-synterp.elpi",
             PRED_FUNC_PATTERN),
    RoleSpec("stdlib", "builtin-doc/elpi-builtin.elpi", PRED_FUNC_PATTERN,
             mangle=(r"^std\.", "")),
    RoleSpec("stdlibfull", "builtin-doc/elpi-builtin.elpi", PRED_FUNC_PATTERN),

    RoleSpec("type", "builtin-doc/coq-builtin.elpi", TYPE_PATTERN),
    RoleSpec("libtype", "elpi/coq-lib.elpi", TYPE_PATTERN),
    RoleSpec("libtype-common", "elpi/coq-lib-common.elpi", TYPE_PATTERN),
    RoleSpec("stdtype", "builtin-doc/elpi-builtin.elpi", TYPE_PATTERN),

    RoleSpec("constructor", "builtin-doc/coq-builtin.elpi", CONSTRUCTOR_PATTERN),
    RoleSpec("stdconstructor", "builtin-doc/elpi-builtin.elpi",
             CONSTRUCTOR_PATTERN),

    RoleSpec("macro", "builtin-doc/coq-builtin.elpi", MACRO_PATTERN),
    RoleSpec("stdlibns", "builtin-doc/elpi-builtin.elpi", NAMESPACE_PATTERN),
]


def _make_role(spec):
    def role_fn(role, rawtext, text, lineno, inliner, options={}, content=[]):
        try:
            full_sha, source_lines = _pin(spec.target_path)
        except (RuntimeError, OSError) as e:
            msg = inliner.reporter.error(str(e), line=lineno)
            return [inliner.problematic(rawtext, rawtext, msg)], [msg]

        name = text
        if spec.mangle is not None:
            name = re.sub(spec.mangle[0], spec.mangle[1], name)

        pattern = re.compile(Template(spec.pattern).safe_substitute(
            name=re.escape(name)))

        target_lineno = None
        for num, line in enumerate(source_lines, 1):
            if pattern.search(line):
                target_lineno = num
                break

        if target_lineno is None:
            msg = inliner.reporter.error(
                f"{role}: '{text}' not found in {spec.target_path} "
                f"using pattern {pattern.pattern}", line=lineno)
            return [inliner.problematic(rawtext, rawtext, msg)], [msg]

        uri = (f"https://github.com/{REPO_ORG}/{REPO_NAME}/blob/"
               f"{full_sha}/{spec.target_path}#L{target_lineno}")
        roles.set_classes(options)
        options.setdefault('classes', []).append('ghref')
        literal = nodes.literal(text, text)
        node = nodes.reference(rawtext, '', literal, refuri=uri, **options)
        return [node], []

    role_fn.__name__ = f"{spec.name}_role"
    return role_fn


def setup(app):
    for spec in ROLE_TABLE:
        app.add_role(spec.name, _make_role(spec))
    # :e:`...` -- inline Elpi-language literal, no file lookup, equivalent to
    # the current `.. role:: e(code) :language: elpi` in etc/tutorial_style.rst
    app.add_role('e', roles.CustomRole('e', roles.code_role,
                                        {'language': 'elpi'}, []))
    return {'version': '1.0', 'parallel_read_safe': True}
