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

all: build test

build: Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq

test: Makefile.test.coq
	@$(MAKE) --no-print-directory -f Makefile.test.coq

theories/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.coq $@
tests/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.test.coq $@
examples/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.test.coq $@

Makefile.coq Makefile.coq.conf: _CoqProject
	@$(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq .merlin
Makefile.test.coq Makefile.test.coq.conf: _CoqProject.test
	@$(COQBIN)/coq_makefile -f _CoqProject.test -o Makefile.test.coq

clean:
	@$(MAKE) -f Makefile.coq $@
	@$(MAKE) -f Makefile.test.coq $@

.PHONY: force all build test

install:
	@$(MAKE) -f Makefile.coq $@
