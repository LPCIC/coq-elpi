with builtins;
with (import <nixpkgs> { }).lib;
let
  master = [
    "coqeal"
    "hierarchy-builder"
    "mathcomp"
    "mathcomp-analysis"
    "mathcomp-bigenough"
    "mathcomp-classical"
    "mathcomp-finmap"
    "mathcomp-real-closed"
    "multinomials"
    "odd-order"
  ];
  common-bundles = listToAttrs (forEach master (p: {
    name = p;
    value.override.version = "master";
  })) // {
    coq-elpi-tests.job = true;
    stdlib.job = true;
    coq-elpi-tests-stdlib.job = true;
    rocq-elpi.job = false;

    mathcomp-single-planB-src.job = false;
    mathcomp-single-planB.job = false;
    mathcomp-single.job = false;

    deriving.job = false;
    reglang.job = false;
  };
in {
  format = "1.0.0";
  attribute = "rocq-elpi";
  coq-attribute = "coq-elpi";
  default-bundle = "rocq-master";
  bundles = {

    "coq-8.20".coqPackages = common-bundles // {
      coq.override.version = "8.20";
      coq-elpi.override.elpi-version = "2.0.7";
      coq-elpi-tests-stdlib.job = false;
    };

    "rocq-9.0".coqPackages = common-bundles // {
      coq.override.version = "9.0";
      coq-elpi.override.elpi-version = "2.0.7";
    };

    "rocq-master" = {
      rocqPackages = {
        rocq-core.override.version = "#18903";
        rocq-elpi.override.elpi-version = "2.0.7";
        stdlib.override.version = "master";
        bignums.override.version = "master";
      };
      coqPackages = common-bundles // {
        coq.override.version = "#18903";
        coq-elpi.override.elpi-version = "2.0.7";
        stdlib.override.version = "master";
        bignums.override.version = "master";
      };
    };

    /* uncomment bundle below if min and max elpi version start to differ
       "coq-master-min-elpi" = { rocqPackages = {
         rocq-core.override.version = "master";
         rocq-elpi.override.elpi-version = "2.0.7";
         stdlib.override.version = "master";
         bignums.override.version = "master";
       }; coqPackages = common-bundles // {
         coq.override.version = "master";
         coq-elpi.override.elpi-version = "2.0.7";
         stdlib.override.version = "master";
         bignums.override.version = "master";
       }; };
    */

  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };
  cachix.coq-elpi.authToken = "CACHIX_AUTH_TOKEN";

}
