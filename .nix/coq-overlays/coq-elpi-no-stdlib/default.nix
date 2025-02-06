{ lib, coq-elpi, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "coq-elpi-no-stdlib";
  opam-name = "coq-elpi";

  propagatedBuildInputs =
    lib.filter (d: d?pname && d.pname != "stdlib")
      coq-elpi.propagatedBuildInputs;
} coq-elpi
