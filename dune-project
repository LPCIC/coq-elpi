(lang dune 3.13)
(using coq 0.8)
(name coq-elpi)
(generate_opam_files)

(source (github LPCIC/coq-elpi))
(license LGPL-2.1-or-later)
(authors "Enrico Tassi <enrico.tassi@inria.fr>")
(maintainers "Enrico Tassi <enrico.tassi@inria.fr>")

(package
 (name coq-elpi)
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
  stdlib-shims
  (elpi (and (>= 2.0.3) (< 2.1.0~)))
  (coq (and (>= 8.20+rc1) (< 8.21~)))
  ppx_optcomp
  (ocaml-lsp-server :with-dev-setup)))

(package
 (name coq-elpi-tests)
 (synopsis "Technical package to run tests")
 (description "Do not install")
 (depends coq-elpi))
