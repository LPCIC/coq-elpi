OCAMLPATH := $(OCAMLPATH):$(shell pwd)/elpi
PATH := $(shell pwd)/coq/bin:$(PATH)
OCAMLDEP := ocamlfind ocamldep
CAMLOPTLINK := ocamlfind ocamlopt -rectypes -thread -linkpkg -dontlink camlp5.gramlib,unix,str
export OCAMLPATH
export OCAMLLIBS = -package elpi -I src
export PATH
export OCAMLDEP
export VERBOSE=1
export CAMLOPTLINK

all: Makefile.coq elpi/elpi.cmxa elpi/META.elpi 
	$(MAKE) -f Makefile.coq $@

Makefile.coq: coq/bin/coq_makefile coq/bin/coqdep coq/bin/coqc coq/bin/coqtop _CoqProject
	coq/bin/coq_makefile -f _CoqProject -o $@

coq/%: coq
	$(MAKE) -C coq/ -j2 $*

elpi/%: elpi
	$(MAKE) -C elpi/ $*

coq:
	git submodule update --init coq
	cd coq/ && ./configure -local -debug -annotate && make states

elpi:
	git submodule update --init elpi
