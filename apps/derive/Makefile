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

coverage:
	@for F in $(wildcard theories/derive/*.v); do\
		D=`basename $$F .v`;\
		T="tests/test_$${D}.v";\
		N=`grep -E "^(Fail )?Elpi derive.$$D" $$T 2>/dev/null| wc -l`;\
		OK=`grep -E "^Elpi derive.$$D" $$T 2>/dev/null| wc -l`;\
		printf "====== %-10s (%2d/%-2d)\n" $$D $$OK $$N;\
		grep -E "^Fail Elpi derive.$$D" $$T 2>/dev/null;\
	done || true

