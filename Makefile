OCAMLPATH := $(OCAMLPATH):$(shell pwd)/elpi
PATH := $(shell pwd)/coq/bin:$(PATH)
export OCAMLPATH
export PATH

all: Makefile.coq elpi/elpi.cmxa elpi/elpi.cma
	@$(MAKE) --no-print-directory -f Makefile.coq opt
	@$(MAKE) --no-print-directory -f Makefile.coq byte

Makefile.coq: coq/bin/coq_makefile coq/bin/coqdep coq/bin/coqc coq/bin/coqtop _CoqProject
	@coq/bin/coq_makefile -f _CoqProject -o $@

coq/bin/%: coq/config/coq_config.ml
	@$(MAKE) --no-print-directory -C coq/ -j2 bin/$*

elpi/elpi.cmxa: elpi/Makefile
	@$(MAKE) --no-print-directory -C elpi/
elpi/elpi.cma: elpi/Makefile
	@$(MAKE) --no-print-directory -C elpi/ byte

coq/config/coq_config.ml:
	git submodule update --init coq
	cd coq/ && ./configure -local -debug -annotate && make -j2
	cp etc/coq-elpi.lang coq/ide/

elpi/Makefile:
	git submodule update --init elpi

run:
	coq/bin/coqide theories/*.v

clean:
	@$(MAKE) -f Makefile.coq clean
