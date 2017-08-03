OCAMLPATH := $(OCAMLPATH):$(shell pwd)/elpi/findlib/
PATH := $(shell pwd)/coq/bin:$(PATH)
export OCAMLPATH
export PATH

ifeq "$(COQBIN)" ""
COQBIN=coq/bin/
endif

ifeq "$(ELPIDIR)" ""
ELPIDIR=elpi/findlib/elpi/
endif

DEPS=$(ELPIDIR)elpi.cmxa $(ELPIDIR)elpi.cma $(COQBIN)/coq_makefile

all: Makefile.coq $(DEPS)
	@$(MAKE) --no-print-directory -f Makefile.coq opt
	@if [ -x $(COQBIN)/coqtop.byte ]; then $(MAKE) --no-print-directory -f Makefile.coq byte; fi

theories/%.vo: Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq $@

Makefile.coq Makefile.coq.conf:  src/coq_elpi_config.ml $(COQBIN)/coq_makefile $(COQBIN)/coqdep $(COQBIN)/coqtop _CoqProject
	@$(COQBIN)/coq_makefile -bypass-API -f _CoqProject -o Makefile.coq

src/coq_elpi_config.ml:
	echo "let elpi_dir = \"$(ELPIDIR)\";;" > $@

# submodules
coq/bin/%: coq/config/coq_config.ml
	@$(MAKE) --no-print-directory -C coq/ -j2 bin/$*

elpi/findlib/elpi/elpi.cmxa: elpi/Makefile
	@$(MAKE) --no-print-directory -C elpi/
elpi/findlib/elpi/elpi.cma: elpi/Makefile
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
	@$(MAKE) -f Makefile.coq $@

include Makefile.coq.conf

install:
	@$(MAKE) -f Makefile.coq $@
	cp $(ELPIDIR)/*.elpi ./*.elpi $(COQMF_COQLIB)/user-contrib/elpi/
	-cp etc/coq-elpi.lang $(COQMF_COQLIB)/ide/
