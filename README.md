# coq-elpi
Coq plugin embedding ELPI

## What is ELPI
[ELPI](https://github.com/LPCIC/elpi) provides an easy-to-embed 
implementation of λProlog, a programming language well suited to
express transformations of abstract syntax trees with binders.  

## What is coq-elpi
Coq-elpi provides a Coq plugin that embeds ELPI.
It also provides a way to embed Coq's terms into λProlog using
the Higher-Order Abstract Syntax) approach
([HOAS](https://en.wikipedia.org/wiki/Higher-order_abstract_syntax))
and a way to read terms back.  In addition to that it exports to ELPI a
set of Coq's primitives, e.g. printing a message, accessing the
environment of theorems and data types, defining a new constant and so on.
Finally is provides a quotation and anti-quotation for Coq's syntax in
λProlog.  E.g. `{{nat}}` is expanded to the type name of natural numbers,
or `{{A -> B}}` to the representation of a product by unfolding the `->`
notation.

## What is the purpose of all that
Provide a scripting language to Coq well suited to express manipulation
of terms.  One can use such language to implement new features, like
code generation "à la derive".
Finally ELPI extends λProlog with a (still under study) language to declare and
manipulate higher order constraints. The aim to provide good language support
to express algorithms like higher order unification and type inference for
Coq's terms.  In particular one can extend the HOAS idea also to unification
variables, i.e. reuse λProlog's meta variables to implement Coq's ones.

