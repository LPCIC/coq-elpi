OCAMLPATH := $(OCAMLPATH):$(shell pwd)/elpi
PATH := $(shell pwd)/coq/bin:$(PATH)
OCAMLDEP := ocamlfind ocamldep
CAMLOPTLINK := ocamlfind ocamlopt -rectypes -thread -linkpkg -dontlink camlp5.gramlib,unix,str
export OCAMLPATH
export OCAMLLIBS = -package elpi -I src
export PATH
export OCAMLDEP
#export VERBOSE=1
export CAMLOPTLINK
export ZDEBUG=-g

all: Makefile.coq elpi/elpi.cmxa elpi/META.elpi 
	@$(MAKE) --no-print-directory -f Makefile.coq $@

Makefile.coq: coq/bin/coq_makefile coq/bin/coqdep coq/bin/coqc coq/bin/coqtop _CoqProject
	@coq/bin/coq_makefile -f _CoqProject -o $@

coq/%: coq
	@$(MAKE) --no-print-directory -C coq/ -j2 $*

elpi/%: elpi
	@$(MAKE) --no-print-directory -C elpi/ $*

coq:
	git submodule update --init coq
	cd coq/ && ./configure -local -debug -annotate && make states
	cp etc/coq-elpi.lang coq/ide/

elpi:
	git submodule update --init elpi

run:
	coq/bin/coqide theories/test*.v

clean:
	@$(MAKE) -f Makefile.coq $@
