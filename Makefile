
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

APPS=$(addprefix apps/, derive eltac NES locker)

ifeq "$(COQ_ELPI_ALREADY_INSTALLED)" ""
DOCDEP=build
else
DOCDEP=
endif

ifndef DOCDIR
DOCDIR=$(shell $(COQBIN)/coqc -where)/../../share/doc/coq-elpi
endif

ifndef COQDOCINSTALL
COQDOCINSTALL=$(DESTDIR)$(DOCDIR)
endif


all:
	$(MAKE) build-core
	$(MAKE) test-core
	$(MAKE) examples
	$(MAKE) build-apps
	$(MAKE) test-apps

build-core: Makefile.coq $(DEPS)
	@echo "########################## building plugin ##########################"
	@if [ -x $(COQBIN)/coqtop.byte ]; then \
		$(MAKE) --no-print-directory -f Makefile.coq bytefiles; \
	fi
	@$(MAKE) --no-print-directory -f Makefile.coq opt

build-apps: build-core
	@echo "########################## building APPS ############################"
	@$(foreach app,$(APPS),$(MAKE) -C $(app) build &&) true

build: build-core build-apps

test-core: Makefile.test.coq $(DEPS) build-core
	@echo "########################## testing plugin ##########################"
	@$(MAKE) --no-print-directory -f Makefile.test.coq

test-apps: build-apps
	@echo "########################## testing APPS ############################"
	@$(foreach app,$(APPS),$(MAKE) -C $(app) test &&) true

test: test-core test-apps

examples: Makefile.examples.coq $(DEPS) build-core
	@echo "############################ examples ############################"
	@$(MAKE) --no-print-directory -f Makefile.examples.coq

doc: $(DOCDEP)
	@echo "########################## generating doc ##########################"
	@mkdir -p doc
	@$(foreach tut,$(wildcard examples/tutorial*$(ONLY)*.v),\
		echo ALECTRYON $(tut) && ./etc/alectryon_elpi.py \
		    --frontend coq+rst \
			--output-directory doc \
		    --pygments-style vs \
			-R theories elpi -Q src elpi \
			$(tut) &&) true
	@cp stlc.html doc/
	@cp etc/tracer.png doc/

.merlin: force
	@rm -f .merlin
	@$(MAKE) --no-print-directory -f Makefile.coq $@

.PHONY: force build all test doc

Makefile.coq Makefile.coq.conf: src/coq_elpi_builtins_HOAS.ml src/coq_elpi_config.ml _CoqProject
	@$(COQBIN)/coq_makefile -f _CoqProject -o Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq .merlin
Makefile.test.coq Makefile.test.coq.conf: _CoqProject.test
	@$(COQBIN)/coq_makefile -f _CoqProject.test -o Makefile.test.coq
Makefile.examples.coq Makefile.examples.coq.conf: _CoqProject.examples
	@$(COQBIN)/coq_makefile -f _CoqProject.examples -o Makefile.examples.coq
src/coq_elpi_builtins_HOAS.ml: elpi/coq-HOAS.elpi Makefile.coq.local
	echo "(* Automatically generated from $<, don't edit *)" > $@
	echo "(* Regenerate via 'make $@' *)" >> $@
	echo "let code = {|" >> $@
	cat $< >> $@
	echo "|}" >> $@

src/coq_elpi_config.ml:
	echo "let elpi_dir = \"$(abspath $(ELPIDIR))\";;" > $@

clean: Makefile.coq Makefile.test.coq
	@$(MAKE) -f Makefile.coq $@
	@$(MAKE) -f Makefile.test.coq $@
	@$(foreach app,$(APPS),$(MAKE) -C $(app) $@ &&) true

include Makefile.coq.conf
V_FILES_TO_INSTALL := \
  $(filter-out theories/wip/%.v,\
  $(COQMF_VFILES))

install:
	@echo "########################## installing plugin ############################"
	@$(MAKE) -f Makefile.coq $@ VFILES="$(V_FILES_TO_INSTALL)"
	@if [ -x $(COQBIN)/coqtop.byte ]; then \
		$(MAKE) -f Makefile.coq $@-byte VFILES="$(V_FILES_TO_INSTALL)"; \
	fi
	-cp etc/coq-elpi.lang $(COQMF_COQLIB)/ide/
	@echo "########################## installing APPS ############################"
	@$(foreach app,$(APPS),$(MAKE) -C $(app) $@ &&) true
	@echo "########################## installing doc ############################"
	-mkdir -p $(COQDOCINSTALL)
	-cp doc/* $(COQDOCINSTALL)
	@echo "########################## installed ############################"


# compile just one file
theories/%.vo: force
	@$(MAKE) --no-print-directory -f Makefile.coq $@
tests/%.vo: force build-core Makefile.test.coq
	@$(MAKE) --no-print-directory -f Makefile.test.coq $@
examples/%.vo: force build-core Makefile.test.coq
	@$(MAKE) --no-print-directory -f Makefile.test.coq $@

SPACE=$(XXX) $(YYY)
apps/%.vo: force
	@$(MAKE) -C apps/$(word 1,$(subst /, ,$*)) \
		$(subst $(SPACE),/,$(wordlist 2,99,$(subst /, ,$*))).vo

OPAM_SUITE=released
release:
	TAG=`git tag --sort=-v:refname|head -1`;\
	echo "Publishing tag $$TAG in suite $(OPAM_SUITE)";\
	echo "Hit ^C to stop, or type options (eg -n fro dry run) and return to continue:";\
	read OPTS;\
	opam-publish --tag=$$TAG --packages-directory=$(OPAM_SUITE)/packages \
		--repo=coq/opam-coq-archive -v $${TAG##v} $$OPTS \
		https://github.com/LPCIC/coq-elpi/releases/download/$$TAG/coq-elpi-$${TAG##v}.tar.gz

release-rc: OPAM_SUITE=extra-dev
release-rc: release