{ coq-elpi, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "coq-elpi-tests-stdlib";

  propagatedBuildInputs = coq-elpi.propagatedBuildInputs
    ++ [ coqPackages.stdlib ];

  buildPhase = ''
    make test-stdlib
    make examples-stdlib
    make test-apps-stdlib
  '';
  installPhase = ''
    echo "nothing to install"
  '';
} coq-elpi
