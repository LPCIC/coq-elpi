dune = dune $(1) $(DUNE_$(1)_FLAGS)

all:
	$(call dune,build)
.PHONY: all

build-core:
	$(call dune,build) theories
.PHONY: build-core

build-apps:
	$(call dune,build) $$(find apps -type d -name theories)
.PHONY: build-apps

build:
	$(call dune,build) @install
.PHONY: build

test-core:
	$(call dune,runtest) tests
.PHONY: test-core

test-apps:
	$(call dune,build) $$(find apps -type d -name tests)
.PHONY: test-apps

test:
	$(call dune,runtest)
	$(call dune,build) $$(find apps -type d -name tests)
.PHONY: test

examples:
	$(call dune,build) examples
.PHONY: examples

doc: build
	@echo "########################## generating doc ##########################"
	@mkdir -p doc
	@$(foreach tut,$(wildcard examples/tutorial*$(ONLY)*.v),\
		echo ALECTRYON $(tut) && OCAMLPATH=$(shell pwd)/_build/install/default/lib ./etc/alectryon_elpi.py \
		    --frontend coq+rst \
			--output-directory doc \
		    --pygments-style vs \
			-R $(shell pwd)/_build/install/default/lib/coq/user-contrib/elpi elpi \
			$(tut) &&) true
	@cp stlc.html doc/
	@cp etc/tracer.png doc/

clean:
	$(call dune,clean)
.PHONY: clean

install:
	$(call dune,build) -p coq-elpi
	$(call dune,install) coq-elpi
.PHONY: install

nix:
	nix-shell --arg do-nothing true --run "updateNixToolBox && genNixActions"
.PHONY: nix
