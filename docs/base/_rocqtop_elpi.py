##########################################################################
# Portions of this file are adapted from the Rocq Prover's own Sphinx
# manual tooling (doc/tools/rocqrst/{repl/rocqtop.py,repl/ansicolors.py,
# rocqdomain.py} as of https://github.com/rocq-prover/rocq, "master"),
# Copyright INRIA, CNRS and contributors, distributed under the GNU Lesser
# General Public License Version 2.1 (see coq-elpi's own LICENSE file,
# also LGPL-2.1-or-later).
##########################################################################
"""
A ``.. rocqtop::`` Sphinx directive that runs Coq/Rocq (and embedded Elpi,
via ``lp:{{ ... }}``) code blocks through a real ``rocq top`` REPL at build
time and renders the captured output -- so every code sample in the coq-elpi
manual is guaranteed to actually type-check, rather than being a static
transcript that can silently drift from reality.

This is a vendored and adapted port of the Rocq manual's own ``.. rocqtop::``
mechanism (see the module docstring of ``repl/rocqtop.py`` there, and
``doc/sphinx/README.rst`` for the directive's user-facing documentation).
Two things are genuinely new here, everything else is a direct port:

- ``split_lines`` is extended to not treat a ``.`` inside an ``lp:{{ ... }}``
  quotation (or a Coq-side antiquotation re-entry ``{{ ... }}`` nested
  inside one) as ending a Coq sentence -- Elpi clauses very commonly end
  with ``.`` at the end of a line, which would otherwise be misread as the
  end of the enclosing Coq vernacular sentence.
- input highlighting uses coq-elpi's own ``CoqElpiLexer`` (Pygments-based,
  see ``_pygments_elpi.py``) instead of the Rocq manual's ``rocqdoc``
  sub-lexer, since it also needs to colorize the embedded Elpi.
- ``RocqTop.__enter__`` disables the pty's canonical (line-buffered) mode.
  coq-elpi's ``lp:{{ ... }}`` quotations routinely make a single Coq
  "sentence" (everything up to the outer ``.``) several KB long -- much
  bigger than anything in a plain-Coq manual. Sending that as one long pty
  line (required so rocqtop doesn't print a spurious continuation prompt
  after every embedded newline, polluting the captured output -- see
  ``RocqTop.sendone``) can exceed the kernel's canonical-mode per-line
  buffer (Linux's ``N_TTY_BUF_SIZE``/``MAX_CANON``, 4096 bytes) and
  deadlock: the write blocks because the buffer is full, while rocqtop's
  read blocks waiting for the newline that can never arrive. Raw mode
  removes that limit; rocqtop does its own sentence-boundary detection
  (it doesn't rely on getting one pty line at a time), so this is safe.

Not ported: the ``RocqDomain`` semantic-markup machinery (``.. cmd::``,
``.. tacn::``, indices, bibtex, the notations grammar, LaTeX support) --
that is Rocq-manual-specific apparatus for documenting Coq's own vernacular
grammar formally, well beyond what this manual needs. Only the REPL driver
and the ``.. rocqtop::`` directive/transform pair are ported.
"""

import os
import re
import shlex
import tempfile
import termios

import pexpect
from docutils import nodes
from docutils.parsers.rst import Directive, directives
from docutils.transforms import Transform
from sphinx.errors import ExtensionError
from sphinx.util.logging import get_node_location

from _pygments_elpi import CoqElpiLexer

# == REPL driver (vendored from doc/tools/rocqrst/repl/rocqtop.py) ==========


class RocqTopError(Exception):
    def __init__(self, err, last_sentence, before):
        super().__init__()
        self.err = err
        self.before = before
        self.last_sentence = last_sentence


class RocqTop:
    """Create an instance of rocq top.

    Use this as a context manager: no instance of rocq top is created until
    you call `__enter__`. rocq top is terminated when you `__exit__` the
    context manager.

    Sentence parsing is very basic for now (a "." in a quoted string will
    confuse it).

    When environment variable ROCQ_DEBUG_REFMAN is set, all the input we
    send to rocq top is copied to a temporary file "/tmp/rocqdomainXXXX.v".
    """

    ROCQTOP_PROMPT = re.compile("\r\n[^< \r\n]+ < ")

    def __init__(self, rocqbin=None, color=False, args=None):
        """Configure a rocq top instance (but don't start it yet).

        :param rocqbin: The path to rocq; uses $COQBIN by default, falling
                         back to "rocq"
        :param color:   When True, tell "rocq top" to produce ANSI color
                         codes (see parse_ansi below)
        :param args:    Additional arguments to "rocq top".
        """
        self.rocqbin = rocqbin or os.path.join(os.getenv("COQBIN", ""), "rocq")
        if not pexpect.utils.which(self.rocqbin):
            raise ValueError("'{}: not found".format(self.rocqbin))
        self.args = ["top"] + (args or []) + ["-q"] + ["-color", "on"] * color
        self.rocqtop = None
        self.debugfile = None

    def __enter__(self):
        if self.rocqtop:
            raise ValueError("This module isn't re-entrant")
        self.rocqtop = pexpect.spawn(self.rocqbin, args=self.args, echo=False, encoding="utf-8")
        self.rocqtop.delaybeforesend = 0
        # Disable canonical (line-buffered) mode -- see the module docstring
        # for why: without this, a long lp:{{ ... }} sentence flattened to
        # one pty line can deadlock the write.
        attrs = termios.tcgetattr(self.rocqtop.child_fd)
        attrs[3] &= ~termios.ICANON
        termios.tcsetattr(self.rocqtop.child_fd, termios.TCSANOW, attrs)
        if os.getenv("ROCQ_DEBUG_REFMAN"):
            self.debugfile = tempfile.NamedTemporaryFile(
                mode="w+", prefix="rocqdomain", suffix=".v", delete=False, dir="/tmp/")
        self.next_prompt()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.debugfile:
            self.debugfile.close()
            self.debugfile = None
        self.rocqtop.kill(9)

    def next_prompt(self):
        """Wait for the next rocq top prompt, and return the output preceding it."""
        self.rocqtop.expect(RocqTop.ROCQTOP_PROMPT, timeout=10)
        return self.rocqtop.before

    def sendone(self, sentence):
        """Send a single sentence to rocq top.

        :sentence: One Rocq sentence (otherwise, rocq top will produce
                   multiple prompts and we'll get confused)
        """
        # rocq top's interactive reader prints a fresh continuation prompt
        # after every real newline it reads, even mid-sentence -- flattening
        # to one line (as the Rocq manual's own driver does) avoids that
        # prompt spam ending up captured as bogus "output". Elpi's `%`
        # comments are newline-terminated, so they must be stripped first
        # (inside lp:{{ }} quotations only -- `%` outside one is a Coq
        # notation-scope delimiter, e.g. `3%Z`, not a comment) or collapsing
        # newlines would let them silently swallow the code after them.
        sentence = _strip_elpi_line_comments(sentence)
        sentence = re.sub(r"[\r\n]+", " ", sentence).strip()
        try:
            if self.debugfile:
                self.debugfile.write(sentence + "\n")
            self.rocqtop.sendline(sentence)
            output = self.next_prompt()
        except Exception as err:
            raise RocqTopError(err, sentence, self.rocqtop.before)
        return output

    def send_initial_options(self):
        """Options to send when starting the toplevel and after a Reset Initial."""
        self.sendone('Set Rocqtop Exit On Error.')
        self.sendone('Set Warnings "+default".')


# == ANSI color parsing (vendored from doc/tools/rocqrst/repl/ansicolors.py) =


def _parse_ansi_color(style, offset):
    color = style[offset] % 10
    names = {0: "black", 1: "red", 2: "green", 3: "yellow", 4: "blue",
             5: "magenta", 6: "cyan", 7: "white", 9: "default"}
    if color in names:
        return names[color], 1
    if color == 8:
        nxt = style[offset + 1]
        if nxt == 5:
            return "index-{}".format(style[offset + 1]), 2
        elif nxt == 2:
            return "rgb-{}-{}-{}".format(*style[offset + 1:offset + 4]), 4
        raise ValueError("{}, {}".format(style, offset))
    raise ValueError()


def _parse_ansi_style(style, acc):
    offset = 0
    while offset < len(style):
        head = style[offset]
        simple = {0: "reset", 1: "bold", 3: "italic", 4: "underline",
                  7: "negative", 22: "no-bold", 23: "no-italic",
                  24: "no-underline", 27: "no-negative"}
        if head in simple:
            acc.append(simple[head])
        else:
            color, suboffset = _parse_ansi_color(style, offset)
            offset += suboffset - 1
            if 30 <= head < 40:
                acc.append("fg-{}".format(color))
            elif 40 <= head < 50:
                acc.append("bg-{}".format(color))
            elif 90 <= head < 100:
                acc.append("fg-light-{}".format(color))
            elif 100 <= head < 110:
                acc.append("bg-light-{}".format(color))
        offset += 1


def parse_ansi(code):
    """Parse an ansi code (a ';'-separated sequence of ANSI codes, without
    the leading '\\x1b[' or the final 'm') into a list of CSS classes."""
    classes = []
    if code == "37":
        pass  # ignore white fg
    else:
        _parse_ansi_style([int(c) for c in code.split(';')], classes)
    return ["ansi-" + cls for cls in classes]


class AnsiColorsParser:
    """Parse ANSI-colored output from rocqtop into Sphinx nodes.

    (A fork of sphinx-contrib's ansi.py, released under a BSD license --
    Rocqtop's raw output crashes the original, which doesn't expect the
    extended codes Rocq emits.)
    """

    COLOR_PATTERN = re.compile('\x1b\\[([^m]+)m')

    def __init__(self):
        self.new_nodes, self.pending_nodes = [], []

    def _finalize_pending_nodes(self):
        self.new_nodes.extend(self.pending_nodes)
        self.pending_nodes = []

    def _add_text(self, raw, beg, end):
        if beg < end:
            text = raw[beg:end]
            if self.pending_nodes:
                self.pending_nodes[-1].append(nodes.Text(text))
            else:
                self.new_nodes.append(nodes.inline('', text))

    def colorize_str(self, raw):
        last_end = 0
        for match in AnsiColorsParser.COLOR_PATTERN.finditer(raw):
            self._add_text(raw, last_end, match.start())
            last_end = match.end()
            classes = parse_ansi(match.group(1))
            if 'ansi-reset' in classes:
                self._finalize_pending_nodes()
            else:
                node = nodes.inline()
                self.pending_nodes.append(node)
                node['classes'].extend(classes)
        self._add_text(raw, last_end, len(raw))
        self._finalize_pending_nodes()
        return self.new_nodes


# == Highlighting input sentences (new: Pygments/CoqElpiLexer, not rocqdoc) ==

# Reuse Pygments' own HtmlFormatter class-name algorithm (not just a plain
# walk-up to the nearest STANDARD_TYPES ancestor), so a custom coq-elpi token
# subtype like Name.ElpiFunction gets the same compound class string here
# ("n n-ElpiFunction") as it would from a plain `.. code-block:: elpi`
# (which goes through Sphinx's own Pygments pipeline) -- otherwise the two
# renderings of the same lexer disagree and custom.css's `.n-ElpiFunction`
# etc. rules only ever apply to one of them.
from pygments.formatters.html import HtmlFormatter

_html_formatter = HtmlFormatter()


def highlight_using_pygments(sentence):
    """Lex sentence using coq-elpi's CoqElpiLexer, and yield inline nodes for
    each token -- the coq-elpi equivalent of the Rocq manual's
    highlight_using_rocqdoc, extended to also colorize embedded Elpi."""
    for tok_type, value in CoqElpiLexer().get_tokens(sentence):
        if not value:
            continue
        cls = _html_formatter._get_css_classes(tok_type).strip()
        yield nodes.inline(value, value, classes=cls.split() if cls else [])


# == The .. rocqtop:: directive + transform (vendored from rocqdomain.py) ===


class RocqtopDirective(Directive):
    """A reST directive to describe interactions with rocq top.
    See docs/base/README.rst for the directive's options.
    """
    has_content = True
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = True
    # :assert: a regex that must be found (re.search, case-insensitive,
    # DOTALL) somewhere in the block's captured output, or the build fails --
    # the equivalent, for a live rocqtop session, of elpi's own manual's
    # `.. elpi::` :assert: option (docs/engine/engine.py there). This is
    # what replaces the old Alectryon tutorials' hand-captured
    # `.. mquote::` blocks: instead of a prose transcript that can silently
    # drift from reality, the real output is re-checked on every build.
    option_spec = {'name': directives.unchanged, 'assert': directives.unchanged}
    directive_name = "rocqtop"

    def run(self):
        # Uses a 'container' instead of a 'literal_block' to disable
        # Pygments-based post-processing (we could also set rawsource to '')
        content = '\n'.join(self.content)
        args = self.arguments[0].split()
        # The 'highlight' class isn't cosmetic: sphinx_rtd_theme's bundled
        # pygments.css scopes every token color rule as `.highlight .kn`
        # etc., so without an ancestor with this exact class, highlighting
        # from highlight_using_pygments (below) renders as plain text, even
        # though the individual <span> token classes are correct.
        node = nodes.container(content, rocqtop_options=set(args),
                                rocqtop_assert=self.options.get('assert'),
                                classes=['rocqtop', 'literal-block', 'highlight'])
        self.add_name(node)
        return [node]


def _quotation_mask(source):
    """One boolean per character of `source`: True while inside an
    ``lp:{{ ... }}`` quotation (or a Coq-side antiquotation re-entry
    ``{{ ... }}`` nested inside one) -- tracked simply as ``{{``/``}}``
    nesting depth, since both the quotation delimiters and the antiquotation
    re-entry delimiters use the same literal tokens. While True, a '.'
    belongs to the embedded Elpi/Coq-in-Elpi source, never to the outer Coq
    sentence, and must not be treated as ending it."""
    n = len(source)
    mask = [False] * n
    depth = 0
    i = 0
    while i < n:
        if source[i:i + 2] == '{{':
            depth += 1
            mask[i] = mask[i + 1] = True
            i += 2
        elif source[i:i + 2] == '}}' and depth > 0:
            depth -= 1
            mask[i] = mask[i + 1] = True
            i += 2
        else:
            mask[i] = depth > 0
            i += 1
    return mask


_PERCENT_COMMENT_RE = re.compile(r'%[^\n]*')


def _strip_elpi_line_comments(sentence):
    """Blank out Elpi ``% ...`` line comments that fall inside an
    ``lp:{{ ... }}`` quotation, so that RocqTop.sendone's newline-to-space
    collapse (needed to avoid spurious rocqtop continuation prompts on
    multi-line input) can't let such a comment silently swallow the code
    that follows it on the next line. ``%`` outside a quotation is left
    untouched -- it's a legitimate Coq notation-scope delimiter there
    (e.g. ``3%Z``), not a comment.

    Not string-aware: a literal ``%`` inside an Elpi string constant would
    also be (wrongly) treated as a comment start. None of this manual's
    content hits that edge case today; revisit if it ever does."""
    mask = _quotation_mask(sentence)
    out = list(sentence)
    for m in _PERCENT_COMMENT_RE.finditer(sentence):
        if mask[m.start()]:
            for i in range(m.start(), m.end()):
                out[i] = ' '
    return ''.join(out)


class RocqtopBlocksTransform(Transform):
    """Filter handling the actual work for the rocqtop directive.

    Adds rocqtop's responses, colorizes input and output, and merges
    consecutive rocqtop directives for better visual rendition.
    """
    default_priority = 10

    @staticmethod
    def is_rocqtop_block(node):
        return isinstance(node, nodes.Element) and 'rocqtop_options' in node

    @staticmethod
    def is_rocqtop_args_field(node):
        return isinstance(node, nodes.field) and node.children[0].rawsource == 'ROCQTOP_ARGS'

    @staticmethod
    def split_lines(source):
        r"""Split Coq input into chunks, which may include single- or
        multi-line comments and embedded ``lp:{{ ... }}`` Elpi quotations.
        Nested (* *) comments are not supported.

        A chunk is a minimal sequence of consecutive lines of the input that
        ends with a '.' or a focusing brace (outside of any lp:{{ }}
        quotation), possibly followed by blanks and/or comments.
        """
        comment = r"\(\*.*\*\)"
        blank = r"[ \t]"
        dot = r"\."
        focusing_brace = r":\s*\{"
        end_of_chunk = re.compile(
            fr"(?:{dot}|{focusing_brace})(?:{blank}*|{comment})*\n")

        src = source.strip()
        mask = _quotation_mask(src)

        chunks = []
        start = 0
        for m in end_of_chunk.finditer(src):
            if mask[m.start()]:
                continue  # '.'/brace sits inside an lp:{{ ... }} quotation
            chunks.append(src[start:m.end()])
            start = m.end()
        if start < len(src):
            chunks.append(src[start:])
        return chunks

    @staticmethod
    def parse_options(node):
        """Parse options according to the description in RocqtopDirective."""
        options = node['rocqtop_options']

        opt_reset = 'reset' in options
        opt_fail = 'fail' in options
        opt_warn = 'warn' in options
        opt_restart = 'restart' in options
        opt_abort = 'abort' in options
        opt_extra = set(opt for opt in options if opt.startswith('extra-'))
        options = options - {'reset', 'fail', 'warn', 'restart', 'abort'}
        options = set(opt for opt in options if not opt.startswith('extra-'))

        unexpected_options = list(options - {'all', 'none', 'in', 'out'})
        if unexpected_options:
            loc = os.path.basename(get_node_location(node))
            raise ExtensionError("{}: Unexpected options for .. rocqtop:: {}".format(loc, unexpected_options))

        if len(options) != 1:
            loc = os.path.basename(get_node_location(node))
            raise ExtensionError("{}: Exactly one display option must be passed to .. rocqtop::".format(loc))

        opt_all = 'all' in options
        opt_input = 'in' in options
        opt_output = 'out' in options

        env_extra = os.environ.get('ROCQRST_EXTRA', '')
        opt_fail = opt_fail or (env_extra != 'all' and len(opt_extra - set(env_extra.split(','))) != 0)
        return {
            'reset': opt_reset,
            'fail': opt_fail,
            'warn': opt_warn or opt_fail,
            'restart': opt_restart,
            'abort': opt_abort,
            'input': opt_input or opt_all,
            'output': opt_output or opt_all,
        }

    @staticmethod
    def block_classes(should_show, contents=None):
        is_empty = contents is not None and re.match(r"^\s*$", contents)
        return ['rocqtop-hidden'] if is_empty or not should_show else []

    @staticmethod
    def make_rawsource(pairs, opt_input, opt_output):
        blocks = []
        for sentence, output in pairs:
            output = AnsiColorsParser.COLOR_PATTERN.sub("", output).strip()
            if opt_input:
                blocks.append(sentence)
            if output and opt_output:
                blocks.append(re.sub("^", "    ", output, flags=re.MULTILINE) + "\n")
        return '\n'.join(blocks)

    def add_rocq_output_1(self, repl, node):
        options = self.parse_options(node)

        pairs = []

        if options['restart']:
            repl.sendone('Restart.')
            repl.sendone('Proof.')
        if options['reset']:
            repl.sendone('Reset Initial.')
            repl.send_initial_options()
        if options['fail']:
            repl.sendone('Unset Rocqtop Exit On Error.')
        if options['warn']:
            repl.sendone('Set Warnings "default".')
        for sentence in self.split_lines(node.rawsource):
            comment = re.compile(r"\s*\(\*.*?\*\)\s*", re.DOTALL)
            wo_comments = re.sub(comment, "", sentence)
            has_content = wo_comments != "" and not wo_comments.isspace()
            output = repl.sendone(sentence) if has_content else ""
            pairs.append((sentence, output))
        if options['abort']:
            repl.sendone('Abort All.')
        if options['fail']:
            repl.sendone('Set Rocqtop Exit On Error.')
        if options['warn']:
            repl.sendone('Set Warnings "+default".')

        assert_re = node.get('rocqtop_assert')
        if assert_re:
            combined = AnsiColorsParser.COLOR_PATTERN.sub(
                "", "\n".join(output for _, output in pairs))
            if not re.search(assert_re, combined, re.IGNORECASE | re.DOTALL):
                loc = get_node_location(node)
                raise ExtensionError(
                    "{}: :assert: {!r} not found in the captured output:\n{}"
                    .format(loc, assert_re, combined))

        dli = nodes.definition_list_item()
        for sentence, output in pairs:
            in_chunks = highlight_using_pygments(sentence)
            dli += nodes.term(sentence, '', *in_chunks, classes=self.block_classes(options['input']))
            if output:
                out_chunks = AnsiColorsParser().colorize_str(output)
                dli += nodes.definition(output, *out_chunks, classes=self.block_classes(options['output'], output))
        node.clear()
        node.rawsource = self.make_rawsource(pairs, options['input'], options['output'])
        node['classes'].extend(self.block_classes(options['input'] or options['output']))
        node += nodes.inline('', '', classes=['rocqtop-reset'] * options['reset'])
        node += nodes.definition_list(node.rawsource, dli)

    def add_rocqtop_output(self):
        """Add rocqtop's responses to a Sphinx AST. One `rocq top` process is
        spawned per source document, and every .. rocqtop:: block in it is
        fed to that same process in document order, so state persists across
        blocks in the same page by default (:reset: blanks it)."""
        arg_fields = self.document.traverse(RocqtopBlocksTransform.is_rocqtop_args_field)
        additional_args = [arg for field in arg_fields for arg in shlex.split(field.children[1].rawsource)]
        with RocqTop(color=True, args=additional_args) as repl:
            repl.send_initial_options()
            for node in self.document.traverse(RocqtopBlocksTransform.is_rocqtop_block):
                try:
                    self.add_rocq_output_1(repl, node)
                except RocqTopError as err:
                    import textwrap
                    msg = ("{}: Error while sending the following to rocqtop:\n{}"
                           "\n  rocqtop output:\n{}"
                           "\n  Full error text:\n{}")
                    indent = "    "
                    loc = get_node_location(node)
                    le = textwrap.indent(str(err.last_sentence), indent)
                    bef = textwrap.indent(str(err.before), indent)
                    fe = textwrap.indent(str(err.err), indent)
                    raise ExtensionError(msg.format(loc, le, bef, fe))

    @staticmethod
    def merge_rocqtop_classes(kept_node, discarded_node):
        discarded_classes = discarded_node['classes']
        if 'rocqtop-hidden' not in discarded_classes:
            kept_node['classes'] = [c for c in kept_node['classes'] if c != 'rocqtop-hidden']

    @staticmethod
    def merge_consecutive_rocqtop_blocks(_app, doctree, _docname):
        """Merge consecutive divs wrapping lists of Coq sentences; keep 'dl's separate."""
        for node in doctree.traverse(RocqtopBlocksTransform.is_rocqtop_block):
            if node.parent:
                rawsources, names = [node.rawsource], set(node['names'])
                for sibling in node.traverse(include_self=False, descend=False,
                                              siblings=True, ascend=False):
                    if RocqtopBlocksTransform.is_rocqtop_block(sibling):
                        RocqtopBlocksTransform.merge_rocqtop_classes(node, sibling)
                        rawsources.append(sibling.rawsource)
                        names.update(sibling['names'])
                        node.extend(sibling.children)
                        node.parent.remove(sibling)
                        sibling.parent = None
                    else:
                        break
                node.rawsource = "\n\n".join(rawsources)
                node['names'] = list(names)

    def apply(self):
        self.add_rocqtop_output()


def setup(app):
    app.add_directive(RocqtopDirective.directive_name, RocqtopDirective)
    app.add_transform(RocqtopBlocksTransform)
    app.connect('doctree-resolved', RocqtopBlocksTransform.merge_consecutive_rocqtop_blocks)
    return {'version': '1.0', 'parallel_read_safe': False}
