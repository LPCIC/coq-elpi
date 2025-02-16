(lang dune 3.13)
(using coq 0.8)
(name rocq-elpi)
;(generate_opam_files)

(source (github LPCIC/coq-elpi))
(license LGPL-2.1-or-later)
(authors "Enrico Tassi <enrico.tassi@inria.fr>")
(maintainers "Enrico Tassi <enrico.tassi@inria.fr>")

(package
 (name rocq-elpi)
 (synopsis "Elpi extension language for Coq")
 (description
  "Coq-elpi provides a Coq plugin that embeds ELPI. It also provides \
   a way to embed Coq's terms into λProlog using the Higher-Order \
   Abstract Syntax approach and a way to read terms back. In addition \
   to that it exports to ELPI a set of Coq's primitives, e.g. printing \
   a message, accessing the environment of theorems and data types, \
   defining a new constant and so on. For convenience it also provides \
   a quotation and anti-quotation for Coq's syntax in λProlog. E.g., \
   `{{nat}}` is expanded to the type name of natural numbers, or \
   `{{A -> B}}` to the representation of a product by unfolding the \
   `->` notation. Finally it provides a way to define new vernacular \
   commands and new tactics.")
 (tags
  ("category:Miscellaneous/Coq Extensions"
   "keyword:λProlog"
   "keyword:higher order abstract syntax"
   "logpath:elpi"))
 (depends
  (ocaml (>= 4.10.0))
  (elpi (and (>= 2.0.3) (< 2.1.0~)))
  (coq (and (>= 8.20+rc1) (< 8.21~)))
  ppx_optcomp
  (ocaml-lsp-server :with-dev-setup)))

(package
 (name rocq-elpi-tests)
 (synopsis "Technical package to run tests")
 (description "Do not install")
 (depends rocq-elpi))

(package
 (name rocq-elpi-tests-stdlib)
 (synopsis "Technical package to run tests depending on Stdlib")
 (description "Do not install")
 (depends rocq-elpi rocq-stdlib))

(package
 (name coq-elpi)
 (allow_empty)
 (depends
  coq-core
  (rocq-elpi (= :version)))
 (synopsis "Compatibility metapackage for Elpi extension language after the Rocq renaming"))
