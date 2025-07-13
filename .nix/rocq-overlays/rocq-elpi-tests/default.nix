{ lib, rocq-elpi, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {

  pname = "rocq-elpi-tests";

  buildPhase = ''
    make test-core
    make examples
    make test-apps
  '';
  installPhase = ''
    echo "nothing to install"
  '';
} rocq-elpi
