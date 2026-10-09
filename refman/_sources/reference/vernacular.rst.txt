Vernacular commands
====================

In order to load Rocq-Elpi use ``From elpi Require Import elpi``.

- ``Elpi Command <qname>`` creates command named ``<qname>`` containing the
  preamble `elpi-command
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template.elpi>`_.
- ``Elpi Tactic <qname>`` creates a tactic ``<qname>`` containing the preamble
  `elpi-tactic
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi>`_.
- ``Elpi Db <dbname> <code>`` creates a Db (a program that is accumulated into
  other programs). ``<code>`` is the initial contents of the Db, including the
  type declaration of its constituting predicates. It understands the
  ``#[phase]`` attribute, see :doc:`synterp-interp`.
- ``Elpi Program <qname> <code>`` lower level primitive letting one create a
  command/tactic with a custom preamble ``<code>``.
- ``From some.load.path Extra Dependency <filename> as <fname>`` declares
  ``<fname>`` as a piece of code that can be accumulated via
  ``Elpi Accumulate File``. The content is given in the external file
  ``<filename>`` to be found in the Rocq load path ``some.load.path``.
- ``Elpi File <fname> <code>.`` declares ``<fname>`` as a piece of code that
  can be accumulated via ``Elpi Accumulate File``. This time the code is
  given in the .v file. It understands the ``#[phase]`` attribute, see
  :doc:`synterp-interp`.
- ``Elpi Accumulate [<dbname>|<qname>] [<code>|File [Signature] <fname>|Db [Header] <dbname>]``
  adds code to the current program (or ``<dbname>`` or ``<qname>`` if
  specified). The code can be verbatim, from a file or a Db. File names
  ``<fname>`` must have been previously declared with ``Extra Dependency`` or
  ``Elpi File``. Accumulating ``File Signature <fname>`` only adds the
  signature declarations (kinds, types, modes, type abbreviations) from
  ``<fname>`` skipping the code (clauses/rules). Accumulating
  ``Db Header <dbname>``, instead of ``Db <dbname>``, accumulates only the
  first chunk of code associated with the Db, typically the type declaration
  of the predicates that live in the Db. When defining a command or tactic it
  can be useful to first accumulate the Db header, then some code (possibly
  calling the predicate living in the Db), and finally accumulating the
  (full) Db. Note that when a command is executed it may need to be
  (partially) recompiled, e.g. if the Db was updated. In this case all the
  code accumulated after the Db (but not after its header) may need to be
  recompiled. Hence we recommend to accumulate Dbs last. It understands the
  ``#[skip="rex"]`` and ``#[only="rex"]`` attributes which make the command a
  no-op if the Rocq version is matched (or not) by the given regular
  expression. It understands the ``#[phase]`` attribute, see
  :doc:`synterp-interp`. It understands the ``#[local]``, ``#[global]``, and
  ``#[superglobal]`` scope attributes, although only when accumulating to a
  ``<dbname>`` (all accumulations to a program are ``#[superglobal]``).
  Default accumulation to a db is the equivalent of ``#[export]``. See the
  Rocq reference manual for the meaning of these scopes.
- ``Elpi Typecheck [<qname>]`` typechecks the current program (or
  ``<qname>`` if specified). It understands the ``#[phase]`` attribute, see
  :doc:`synterp-interp`.
- ``Elpi Debug <string>`` sets the variable ``<string>``, relevant for
  conditional clause compilation (the ``:if VARIABLE`` clause attribute). It
  understands the ``#[phase]`` attribute, see :doc:`synterp-interp`.
- ``Elpi Trace [[<start> <stop>] <predicate-filter>*|Off]`` enables/disables
  tracing, eventually limiting it to a specific range of execution steps or
  predicate names. It understands the ``#[phase]`` attribute, see
  :doc:`synterp-interp`.
- ``Elpi Trace Browser`` enables/disables tracing for Elpi's trace browser.
- ``Elpi Bound Steps <number>`` limits the number of steps an Elpi program
  can make.
- ``Elpi Print <qname> [<string> <filter>*]`` prints the program ``<qname>``
  to a text file called ``<qname>.txt`` (or ``<string>`` if provided)
  filtering out clauses whose file or clause-name matches ``<filter>``. It
  understands the ``#[phase]`` attribute, see :doc:`synterp-interp`.

where:

- ``<qname>`` is a qualified Rocq name, e.g. ``derive.eq`` or ``my_program``.
- ``<dbname>`` is like ``<qname>`` but lives in a different namespace. By
  convention ``<dbname>`` ends in ``.db``, e.g. ``derive.eq.db``.
- ``<code>`` is verbatim Elpi code, either ``lp:{{ ... }}`` or ``" ... "`` (in
  the latter case, string delimiters need to be escaped following Rocq
  rules, e.g. ``lp:{{ coq.say "hello!" }}`` becomes ``" coq.say ""hello!"" "``).
- ``<filename>`` is a string containing the path of an external file, e.g.
  ``"this_file.elpi"``.
- ``<fname>`` is a qualified Rocq name, e.g. ``foo.elpi`` (note that
  ``Extra Dependency`` only allows simple identifiers).
- ``<start>`` and ``<stop>`` are numbers, e.g. ``17 24``.
- ``<predicate-filter>`` is a regexp against which the predicate name is
  matched, e.g. ``"derive.*"``.
