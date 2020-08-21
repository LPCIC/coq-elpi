
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
ELPIDIR=$(shell ocamlfind query elpi 2>/dev/null)
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
	@$(MAKE) -C apps/derive

theories/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.coq $@
.merlin: force
	@rm -f .merlin
	@$(MAKE) --no-print-directory -f Makefile.coq $@
.PHONY: force

Makefile.coq Makefile.coq.conf:  src/coq_elpi_config.ml _CoqProject
	@$(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq .merlin

src/coq_elpi_config.ml:
	echo "let elpi_dir = \"$(abspath $(ELPIDIR))\";;" > $@

clean:
	@$(MAKE) -f Makefile.coq $@
	@$(MAKE) -C apps/derive clean

include Makefile.coq.conf
V_FILES_TO_INSTALL := \
  $(filter-out theories/wip/%.v,\
  $(filter-out theories/tests/%.v,\
  $(filter-out theories/examples/%.v,\
  $(filter-out theories/ltac/tests/%.v,\
  $(COQMF_VFILES)))))

install:
	@$(MAKE) -f Makefile.coq $@ VFILES="$(V_FILES_TO_INSTALL)"
	@if [ -x $(COQBIN)/coqtop.byte ]; then \
		$(MAKE) -f Makefile.coq $@-byte VFILES="$(V_FILES_TO_INSTALL)"; \
	fi
	-cp etc/coq-elpi.lang $(COQMF_COQLIB)/ide/
	@$(MAKE) -C apps/derive install