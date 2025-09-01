with builtins; with (import <nixpkgs> {}).lib;
let master = [
    "coqeal"
    "hierarchy-builder"
    "mathcomp"
    "mathcomp-analysis"
    "mathcomp-bigenough"
    "mathcomp-finmap"
    "mathcomp-real-closed"
    "multinomials"
    "odd-order"
    "trakt"
  ];
  rocq-common-bundles = {
    rocq-elpi.override.elpi-version = "v3.1.0";
    hierarchy-builder.override.version = "master";
    rocq-elpi-tests.job = true;
  };
  coq-common-bundles = listToAttrs (forEach master (p:
    { name = p; value.override.version = "master"; }))
  // {
    coq-elpi.override.elpi-version = "v3.1.0";
    coq-elpi-tests-stdlib.job = true;

    mathcomp-boot.job = true;
    mathcomp-fingroup.job = true;
    mathcomp-order.job = true;
    mathcomp-ssreflect.job = true;
    mathcomp-algebra.job = true;
    mathcomp-solvable.job = true;
    mathcomp-field.job = true;
    mathcomp-character.job = true;
    mathcomp-classical.job = true;
    mathcomp-reals.job = true;
    mathcomp-experimental-reals.job = true;
    mathcomp-reals-stdlib.job = true;
    mathcomp-analysis-stdlib.job = true;

    bignums.job = true;
    stdlib.job = true;

    mathcomp-single-planB-src.job = false;
    mathcomp-single-planB.job = false;
    mathcomp-single.job = false;

    deriving.job = false;
    reglang.job = false;

    coquelicot.job = false;
    interval.job = false;
    QuickChick.job = false;
    vcfloat.job = false;
}; in
{
  format = "1.0.0";
  attribute = "rocq-elpi";
  coq-attribute = "coq-elpi";
  default-bundle = "coq-8.20";
  bundles = {

    "coq-8.20".coqPackages = coq-common-bundles // {
      coq.override.version = "8.20";
      coq-elpi.override.elpi-version = "v3.1.0";
    };

    "rocq-9.0" = { rocqPackages = rocq-common-bundles // {
      rocq-core.override.version = "9.0";
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "9.0";
      hierarchy-builder.override.version = "master";
    }; };

    "rocq-9.1" = { rocqPackages = rocq-common-bundles // {
      rocq-core.override.version = "9.1";
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "9.1";
      hierarchy-builder.override.version = "master";
    }; };

    "coq-master" = { rocqPackages = rocq-common-bundles // {
      rocq-core.override.version = "master";
      bignums.override.version = "master";
      stdlib.override.version = "master";
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "master";
      bignums.override.version = "master";
      stdlib.override.version = "master";
      hierarchy-builder.override.version = "master";
    }; };

    /* uncomment bundle below if min and max elpi version start to differ
    "coq-master-min-elpi" = { rocqPackages = rocq-common-bundles // {
      rocq-core.override.version = "master";
      rocq-elpi.override.elpi-version = "v3.1.0";
      stdlib.override.version = "master";
      bignums.override.version = "master";
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "master";
      coq-elpi.override.elpi-version = "v3.1.0";
      stdlib.override.version = "master";
      bignums.override.version = "master";
    }; }; */

  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.coq-elpi.authToken = "CACHIX_AUTH_TOKEN";

}
