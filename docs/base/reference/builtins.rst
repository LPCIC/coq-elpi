Builtins and relevant files
=============================

Rocq-Elpi's API surface (the predicates and data types Elpi code can use to
interact with Rocq) is documented in a handful of generated/hand-written
``.elpi`` files. Throughout this manual, inline references like
:builtin:`coq.say` or :type:`term` link directly to the declaration of a
predicate/type inside these files, at the commit the manual was built from.

- `coq-builtin.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin.elpi>`_
  documents the HOAS encoding of Rocq terms and the API to access Rocq.
  Example roles: :builtin:`coq.say`, :type:`term`, :constructor:`app`,
  :macro:`@global!`.
- `coq-builtin-synterp.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin-synterp.elpi>`_
  documents APIs to interact with Rocq at parsing time. Example role:
  :builtin-synterp:`coq.say`.
- `elpi-builtin.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/elpi-builtin.elpi>`_
  documents Elpi's standard library, you may look here for list processing
  code. Example roles: :stdlib:`std.do!` (the ``std.`` prefix is stripped
  before lookup), :stdlibfull:`true` (no prefix stripped), :stdtype:`int`,
  :stdconstructor:`uvar`, :stdlibns:`std`.
- `coq-lib.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/coq-lib.elpi>`_
  provides some utilities to manipulate Rocq terms; it is an addendum to
  coq-builtin. Example roles: :lib:`coq.subst-prod`, :libtype:`coq.indt-spec`.
- `coq-lib-common.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/coq-lib-common.elpi>`_.
  Example roles: :lib-common:`coq.parse-attributes`,
  :libtype-common:`attribute-signature`.
- `elpi-reduction.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-reduction.elpi>`_.
  Example role: :libred:`hd-beta`.
- `elpi-ltac.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi>`_
  the ``coq.ltac.*`` bridge to Ltac1. Example role: :libtac:`refine` (the
  ``coq.ltac.`` prefix is stripped before lookup, e.g. this links to
  ``coq.ltac.refine``).
- `elpi-command-template.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template.elpi>`_
  provides the pre-loaded code for ``Elpi Command`` (execution phase) and
  ``Elpi Tactic``.
- `elpi-command-template-synterp.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-command-template-synterp.elpi>`_
  provides the pre-loaded code for ``Elpi Command`` (parsing phase).
- `elpi-tactic-template.elpi
  <https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-tactic-template.elpi>`_
  provides the pre-loaded code for ``Elpi Tactic`` (note tactics also load
  elpi-command-template.elpi above).
