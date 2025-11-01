{ rocq-elpi, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {

  pname = "rocq-elpi-tests-stdlib";

  propagatedBuildInputs = rocq-elpi.propagatedBuildInputs
    ++ [ rocqPackages.stdlib ];

  buildPhase = ''
    export COQPATH=$ROCQPATH
    make test-stdlib
    make examples-stdlib
    make test-apps-stdlib
  '';
  installPhase = ''
    echo "nothing to install"
  '';
} rocq-elpi
