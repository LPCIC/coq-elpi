all:
	@dune build
.PHONY: all

build-core:
	@dune build theories
.PHONY: build-core

build-apps:
	@dune build $$(find apps -type d -name theories)
.PHONY: build-apps

build:
	@dune build @install
.PHONY: build

test-core:
	@dune build tests
.PHONY: test-core

test-apps:
	@dune build $$(find apps -type d -name tests)
.PHONY: test-apps

test:
	@dune build $$(find . -type d -name tests)
.PHONY: test

examples:
	@dune build examples
.PHONY: examples

# FIXME
#doc: $(DOCDEP)
#	@echo "########################## generating doc ##########################"
#	@mkdir -p doc
#	@$(foreach tut,$(wildcard examples/tutorial*$(ONLY)*.v),\
#		echo ALECTRYON $(tut) && ./etc/alectryon_elpi.py \
#		    --frontend coq+rst \
#			--output-directory doc \
#		    --pygments-style vs \
#			-R theories elpi -Q src elpi \
#			$(tut) &&) true
#	@cp stlc.html doc/
#	@cp etc/tracer.png doc/

clean:
	@dune clean
.PHONY: clean

install:
	@dune build -p coq-elpi
	@dune install coq-elpi
.PHONY: install

nix:
	nix-shell --arg do-nothing true --run "updateNixToolBox & genNixActions"
.PHONY: nix
