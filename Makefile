dune_wrap = $(shell command -v coqc > /dev/null || echo "etc/with-rocq-wrap.sh")
dune = $(dune_wrap) dune $(1) $(DUNE_$(1)_FLAGS) --stop-on-first-error

# This makefile is mostly calling dune and dune doesn't like
# being called in parralel, so we enforce -j1
.NOTPARALLEL:

all:
	$(call dune,build)
	$(call dune,build) builtin-doc
.PHONY: all

build-core:
	$(call dune,build) theories
	$(call dune,build) builtin-doc
.PHONY: build-core

build-apps:
	$(call dune,build) $$(find apps -type d -name theories)
.PHONY: build-apps

build:
	$(call dune,build) -p rocq-elpi @install
	$(call dune,build) builtin-doc
.PHONY: build

all-tests-no-plugins: test-core test-repro test-stdlib test-apps test-apps-stdlib
.PHONY: all-tests-no-plugins

all-tests: all-tests-no-plugins test-plugins
.PHONY: all-tests

test-core:
	$(call dune,runtest) tests
	$(call dune,build) tests

# Check for build reproducibility
test-repro: test-core
	$(dune_wrap) dune coq top --toplevel coqc tests/accumulate1.v -- tests/accumulate1.v
	md5sum tests/accumulate1.vo > md5sum_accumulate1vo_1
	rm -f tests/accumulate1.vo tests/accumulate1.glob
	$(dune_wrap) dune coq top --toplevel coqc tests/accumulate1.v -- tests/accumulate1.v
	md5sum tests/accumulate1.vo > md5sum_accumulate1vo_2
	rm -f tests/accumulate1.vo tests/accumulate1.glob
	diff md5sum_accumulate1vo_1 md5sum_accumulate1vo_2
	rm md5sum_accumulate1vo_1 md5sum_accumulate1vo_2

.PHONY: test-core test-repro

test-apps:
	$(call dune,build) $$(find apps -type d -name tests)
.PHONY: test-apps

test-plugins:
	$(call dune,build) $$(find apps -type d -name tests-plugin)
.PHONY: test-plugins

test-apps-stdlib:
	$(call dune,build) $$(find apps -type d -name tests-stdlib)
.PHONY: test-apps-stdlib

test-stdlib:
	$(call dune,build) tests-stdlib
.PHONY: test-stdlib

all-examples: examples examples-stdlib
.PHONY: all-examples

examples:
	$(call dune,build) examples
.PHONY: examples

examples-stdlib:
	$(call dune,build) examples-stdlib
.PHONY: examples-stdlib

doc:
	@echo "########################## generating doc ##########################"
	@python3 -m venv alectryon
	@alectryon/bin/pip3 install git+https://github.com/gares/alectryon.git@4509235b1b83b256fd15d8dff92ac71666f419a1
	@mkdir -p doc
	@$(foreach tut,$(wildcard examples/tutorial*$(ONLY)*.v),\
		echo ALECTRYON $(tut) && alectryon/bin/python3 etc/alectryon_elpi.py \
		    --frontend coq+rst \
			--output-directory doc \
		    --pygments-style vs \
			--coq-driver vsrocq \
			$(tut) &&) true
	@cp etc/tracer.png doc/

# Sphinx-based reference manual (docs/base -> docs/source -> docs/build).
# `.. rocqtop::` blocks in docs/base/**/*.rst run through a real `rocq top`
# with rocq-elpi loaded, so rocq-elpi must be installed into the opam switch
# `rocq top` resolves against (not just dune-built-in-place), and
# builtin-doc/*.elpi must exist on disk (read by docs/base/_roles_elpi.py).
refman-build:
	$(call dune,build) -p rocq-elpi @install
	$(call dune,build) builtin-doc
	$(call dune,install) rocq-elpi
	rm -rf docs/source docs/build
	cp -r docs/base docs/source
	sed -i "s/@@VERSION@@/$$(git describe --always)/" docs/source/conf.py
	sphinx-build -q -W -b html docs/source docs/build
.PHONY: refman-build

refman-serve: refman-build
	cd docs/build && python3 -m http.server 8000
.PHONY: refman-serve

clean:
	$(call dune,clean)
.PHONY: clean

install:
	$(call dune,install) rocq-elpi
.PHONY: install

nix:
	nix-shell --arg do-nothing true --run "updateNixToolBox && genNixActions"
.PHONY: nix
