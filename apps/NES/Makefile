all: Makefile.coq $(DEPS)
	@$(MAKE) --no-print-directory -f Makefile.coq

theories/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.coq $@

Makefile.coq Makefile.coq.conf: _CoqProject
	@$(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq .merlin

clean:
	@$(MAKE) -f Makefile.coq $@

.PHONY: force

include Makefile.coq.conf
V_FILES_TO_INSTALL := \
  $(filter-out tests/%.v,\
  $(filter-out examples/%.v,\
  $(COQMF_VFILES)))

install:
	@$(MAKE) -f Makefile.coq $@ VFILES="$(V_FILES_TO_INSTALL)"
