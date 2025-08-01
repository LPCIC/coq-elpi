dune_wrap = $(shell command -v coqc > /dev/null || echo "etc/with-rocq-wrap.sh")
dune = $(dune_wrap) dune $(1) $(DUNE_$(1)_FLAGS) --stop-on-first-error
DUNE_IN_FILES = $(shell find . -name "dune.in" | sed -e 's/.in$$//')

# This makefile is mostly calling dune and dune doesn't like
# being called in parralel, so we enforce -j1
.NOTPARALLEL:

all: $(DUNE_IN_FILES)
	$(call dune,build)
	$(call dune,build) builtin-doc
.PHONY: all

# simplify this and get rid of the dune.in files once we require Rocq >= 9.0
%dune: %dune.in
	@rm -f $@
	@echo "; generated by make, do not edit\n" > $@
	@if test -e .coq-dune-files || \
	    (command -v coqc > /dev/null && (coqc --version | grep -q '8.20')) ; then \
	  sed -e 's/@@STDLIB_THEORY@@//' $< | \
	  sed -e 's/@@STDLIB@@//' | \
	  sed -e 's/@@ROCQ_RUNTIME@@/coq-core/g' >> $@ ; \
	else \
	  sed -e 's/@@STDLIB_THEORY@@/(theories Stdlib)/' $< | \
	  sed -e 's/@@STDLIB@@/Stdlib/' | \
	  sed -e 's/@@ROCQ_RUNTIME@@/rocq-runtime/g' >> $@ ; \
	fi
	@chmod a-w $@

dune-files: $(DUNE_IN_FILES)
.PHONE: dune-files

coq-dune-files:
	touch .coq-dune-files
	$(MAKE) dune-files
	$(RM) .coq-dune-files
.PHONE: coq-dune-files

build-core: $(DUNE_IN_FILES)
	$(call dune,build) theories
	$(call dune,build) builtin-doc
.PHONY: build-core

build-apps: $(DUNE_IN_FILES)
	$(call dune,build) $$(find apps -type d -name theories)
.PHONY: build-apps

build: $(DUNE_IN_FILES)
	$(call dune,build) -p rocq-elpi @install
	$(call dune,build) builtin-doc
.PHONY: build

all-tests: test-core test-stdlib test-apps test-apps-stdlib
.PHONY: all-tests

test-core: $(DUNE_IN_FILES)
	$(call dune,runtest) tests
	$(call dune,build) tests
	# Check for build reproducibility
	md5sum _build/default/tests/accumulate1.vo > md5sum_accumulate1vo_1
	rm -f _build/default/tests/accumulate1.vo
	$(call dune,build) --cache=disabled tests
	md5sum _build/default/tests/accumulate1.vo > md5sum_accumulate1vo_2
	diff md5sum_accumulate1vo_1 md5sum_accumulate1vo_2
	rm md5sum_accumulate1vo_1 md5sum_accumulate1vo_2
.PHONY: test-core

test-apps: $(DUNE_IN_FILES)
	$(call dune,build) $$(find apps -type d -name tests)
.PHONY: test-apps

test-apps-stdlib: $(DUNE_IN_FILES)
	$(call dune,build) $$(find apps -type d -name tests-stdlib)
.PHONY: test-apps-stdlib

test-stdlib: $(DUNE_IN_FILES)
	$(call dune,build) tests-stdlib
.PHONY: test-stdlib

all-examples: examples examples-stdlib
.PHONY: all-examples

examples: $(DUNE_IN_FILES)
	$(call dune,build) examples
.PHONY: examples

examples-stdlib: theories-stdlib/dune
	$(call dune,build) examples-stdlib
.PHONY: examples-stdlib

doc: build
	@echo "########################## generating doc ##########################"
	@mkdir -p doc
	@$(foreach tut,$(wildcard examples/tutorial*$(ONLY)*.v),\
		echo ALECTRYON $(tut) && OCAMLPATH=$(shell pwd)/_build/install/default/lib ./etc/alectryon_elpi.py \
		    --frontend coq+rst \
			--output-directory doc \
		    --pygments-style vs \
			-R $(shell pwd)/_build/install/default/lib/coq/user-contrib/elpi_elpi elpi_elpi \
			-R $(shell pwd)/_build/install/default/lib/coq/user-contrib/elpi elpi \
			$(tut) &&) true
	@cp ./_build/default/examples/stlc.txt doc/
	@cp etc/tracer.png doc/

clean:
	$(call dune,clean)
.PHONY: clean

install: $(DUNE_IN_FILES)
	$(call dune,install) rocq-elpi
.PHONY: install

nix:
	nix-shell --arg do-nothing true --run "updateNixToolBox && genNixActions"
.PHONY: nix
