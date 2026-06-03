(lang dune 3.17)
(using coq 0.8)
(name Ext)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name rocq-elpi-ext)
 (synopsis "Ext")
 (description "Ext")
 (depends rocq-elpi))

(package
 (name rocq-elpi-ext-tests)
 (synopsis "Ext")
 (description "Ext")
 (depends rocq-elpi))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
