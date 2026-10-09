# Configuration file for the Sphinx documentation builder.
#
# Modelled on elpi's own docs/base/conf.py (../elpi/docs/base/conf.py).

project = 'Rocq-Elpi'
copyright = '2026, Enrico Tassi and the Rocq-Elpi contributors'
author = 'Enrico Tassi'

# The full version, including alpha/beta/rc tags -- substituted by `sed` at
# build time from `git describe`, exactly like elpi's manual.
release = '@@VERSION@@'

extensions = [
    'sphinx.ext.intersphinx',
    'sphinx.ext.githubpages',
    'sphinx.ext.mathjax',
    '_roles_elpi',
    '_rocqtop_elpi',
]

# Sphinx's default primary domain ('py') shadows any bare role whose name it
# also defines (sphinx.util.docutils.sphinx_domains.role() checks the
# default domain before falling back to roles registered via add_role()),
# and the Python domain happens to define a role named 'type' -- exactly the
# name _roles_elpi.py registers for linking to a builtin-doc/coq-builtin.elpi
# type declaration. This manual has no Python API docs, so there is nothing
# to lose by turning the shortcut off.
primary_domain = None

templates_path = ['_templates']

# The .. rocqtop:: directive renders captured rocq top input/output as
# docutils `inline`/`term`/`definition` nodes (not `literal_block`), since a
# definition list is the natural shape for a sequence of (sentence, output)
# pairs. Sphinx's default smartquotes transform only skips FixedTextElement
# nodes (e.g. literal_block, which `.. code-block::` already uses), so
# without this it silently "corrects" real code/output text -- e.g. turning
# a run of dots in a comment into a single "…" character, or straight
# quotes in coq.say output into curly ones. That's actively misleading in a
# reference manual, so disable it manual-wide rather than restructure the
# rocqtop node tree to dodge the transform.
smartquotes = False

# Keep the helper .py modules out of the toctree/build.
exclude_patterns = ['_pygments_elpi.py', '_roles_elpi.py', '_rocqtop_elpi.py']
master_doc = 'index'

# Register the manual's own Coq/Elpi/Coq-with-embedded-Elpi lexers.
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _pygments_elpi import ElpiLexer, CoqElpiLexer
from sphinx.highlighting import lexers
lexers['elpi'] = ElpiLexer()
lexers['coq'] = CoqElpiLexer()

# The above covers `.. code-block::`/`.. highlight::` (Sphinx's own
# PygmentsBridge, which checks this dict), but not the `:e:` role (and any
# other inline `:code:`-like role): docutils' own `code_role` highlights via
# `docutils.utils.code_analyzer.Lexer`, which calls
# `pygments.lexers.get_lexer_by_name()` directly, bypassing the dict above
# entirely. That resolves 'elpi'/'coq' to whatever Pygments package happens
# to be installed -- e.g. the stock Pygments ElpiLexer lexes the guillemets
# used for printed global names (`:e:`indt «nat»``) as an Error token, since
# it predates that convention. Pre-populating Pygments' own lexer cache
# under each class's `name` makes every lookup path resolve to these same
# patched classes.
import pygments.lexers
pygments.lexers._lexer_cache[ElpiLexer.name] = ElpiLexer
pygments.lexers._lexer_cache[CoqElpiLexer.name] = CoqElpiLexer

intersphinx_mapping = {
    'elpi': ('https://lpcic.github.io/elpi/', None),
}

# -- Options for HTML output -------------------------------------------------

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']
html_css_files = ['custom.css']
