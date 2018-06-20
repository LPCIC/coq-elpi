OCAMLPATH := $(OCAMLPATH):$(shell pwd)/elpi/findlib/
PATH := $(shell pwd)/coq/bin:$(PATH)
export OCAMLPATH
export PATH

# detection of coq
ifeq "$(COQBIN)" ""
COQBIN=$(shell which coqc 2>/dev/null && dirname `which coqc`)
endif
ifeq "$(COQBIN)" ""
COQBIN=coq/bin/
$(info Using coq from the git submodule ./coq/, override via COQBIN or PATH)
else
$(info Using coq found in $(COQBIN), from COQBIN or PATH)
endif
export COQBIN

# detection of elpi
ifeq "$(ELPIDIR)" ""
ELPIDIR=$(shell which elpi 2>/dev/null && elpi -where)
endif
ifeq "$(ELPIDIR)" ""
ELPIDIR=elpi/findlib/elpi
$(info Using elpi from the git submodule ./elpi/, override via ELPIDIR or PATH)
else
$(info Using elpi found in $(ELPIDIR), from ELPIDIR or PATH)
endif
export ELPIDIR

DEPS=$(ELPIDIR)/elpi.cmxa $(ELPIDIR)/elpi.cma $(COQBIN)/coq_makefile

all: Makefile.coq $(DEPS)
	@if [ -x $(COQBIN)/coqtop.byte ]; then \
		$(MAKE) --no-print-directory -f Makefile.coq bytefiles; \
	fi
	@$(MAKE) --no-print-directory -f Makefile.coq opt

theories/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.coq $@
.merlin: force
	@rm -f .merlin
	@$(MAKE) --no-print-directory -f Makefile.coq $@
coqmf/%: force
	@$(MAKE) --no-print-directory -f Makefile.coq $*
.PHONY: force

Makefile.coq Makefile.coq.conf:  src/coq_elpi_config.ml $(COQBIN)/coq_makefile $(COQBIN)/coqdep $(COQBIN)/coqtop _CoqProject
	@$(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq .merlin

src/coq_elpi_config.ml:
	echo "let elpi_dir = \"$(abspath $(ELPIDIR))\";;" > $@

# submodules
coq/bin/%: coq/config/coq_config.ml
	@$(MAKE) --no-print-directory -C coq/ -j2 bin/$*

# to avoid a race we add a fake dependency among these two
elpi/findlib/elpi/elpi.cmxa: elpi/Makefile
	@$(MAKE) --no-print-directory -C elpi/
elpi/findlib/elpi/elpi.cma: elpi/Makefile elpi/findlib/elpi/elpi.cmxa
	@$(MAKE) --no-print-directory -C elpi/ byte

coq/config/coq_config.ml:
	git submodule update --init coq
	cd coq/ && ./configure -profile devel 
	cd coq/ && make -j2 && make -j2 byte
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
	@if [ -x $(COQBIN)/coqtop.byte ]; then \
		$(MAKE) -f Makefile.coq $@-byte; \
	fi
	-cp etc/coq-elpi.lang $(COQMF_COQLIB)/ide/

coverage:
	@for F in $(wildcard theories/derive/*.v); do\
		D=`basename $$F .v`;\
		T="theories/derive/tests/test_$${D}.v";\
		N=`grep -E "^(Fail )?Elpi derive.$$D Coverage" $$T 2>/dev/null| wc -l`;\
		OK=`grep -E "^Elpi derive.$$D Coverage" $$T 2>/dev/null| wc -l`;\
		printf "====== %-10s (%2d/%-2d)\n" $$D $$OK $$N;\
		grep -E "^Fail Elpi derive.$$D Coverage" $$T 2>/dev/null;\
	done

