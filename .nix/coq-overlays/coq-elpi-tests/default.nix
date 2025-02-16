{ lib, coq-elpi, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "coq-elpi-tests";

  buildPhase = ''
    make test-core
    make examples
    make test-apps
  '';
  installPhase = ''
    echo "nothing to install"
  '';
} coq-elpi
