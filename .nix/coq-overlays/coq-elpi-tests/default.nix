{ lib, coq-elpi, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "coq-elpi-tests";

  propagatedBuildInputs =
    lib.filter (d: d?pname && d.pname != "stdlib")
      coq-elpi.propagatedBuildInputs;

  buildPhase = ''
    make test-core
    make examples
    make test-apps
  '';
  installPhase = ''
    echo "nothing to install"
  '';
} coq-elpi
