
# detection of coq
ifeq "$(COQBIN)" ""
COQBIN := $(shell which coqc >/dev/null 2>&1 && dirname `which coqc`)
endif
ifeq "$(COQBIN)" ""
$(error Coq not found, make sure it is installed in your PATH or set COQBIN)
else
$(info Using coq found in $(COQBIN), from COQBIN or PATH)
endif
export COQBIN := $(COQBIN)/

# detection of elpi
ifeq "$(ELPIDIR)" ""
ELPIDIR=$(shell which elpi >/dev/null 2>&1 && elpi -where)
endif
ifeq "$(ELPIDIR)" ""
$(error Elpi not found, make sure it is installed in your PATH or set ELPIDIR)
endif
export ELPIDIR

DEPS=$(ELPIDIR)/elpi.cmxa $(ELPIDIR)/elpi.cma

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

Makefile.coq Makefile.coq.conf:  src/coq_elpi_config.ml _CoqProject
	@$(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq .merlin

src/coq_elpi_config.ml:
	echo "let elpi_dir = \"$(abspath $(ELPIDIR))\";;" > $@

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
	done || true

