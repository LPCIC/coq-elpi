with builtins; with (import <nixpkgs> {}).lib;
let
  default-elpi-version = "3.7.1";
  min-elpi-version = "3.7.1";
  master = [
    "hierarchy-builder"
    "mathcomp"
    "mathcomp-analysis"
    "mathcomp-bigenough"
    "mathcomp-finmap"
    "mathcomp-real-closed"
    "coqeal"
    "ITree"
    "mathcomp-word"
    "mathcomp-zify"
    "multinomials"
    "odd-order"
    "trakt"
  ];
  common-bundles = listToAttrs (forEach master (p:
    { name = p; value.override.version = "master"; }))
  // {
    rocq-elpi.override.elpi-version = default-elpi-version;
    rocq-elpi-tests.job = true;
    rocq-elpi-tests-stdlib.job = true;

    mathcomp-boot.job = true;
    mathcomp-fingroup.job = true;
    mathcomp-order.job = true;
    mathcomp-algebra.job = true;
    mathcomp-solvable.job = true;
    mathcomp-field.job = true;
    mathcomp-character.job = true;
    mathcomp-classical.job = true;
    mathcomp-reals.job = true;
    mathcomp-experimental-reals.job = true;
    mathcomp-reals-stdlib.job = true;
    mathcomp-analysis-stdlib.job = true;

    jasmin.override.version = "main";

    bignums.job = true;
    stdlib.job = true;

    mathcomp-single.job = false;

    deriving.job = false;
    reglang.job = false;

    coquelicot.job = false;
    interval.job = false;
    QuickChick.job = false;
    vcfloat.job = false;

    autosubst.job = false;

    ConCert.job = false;

    ITree.job = false;  # only a dependency of jasmin
}; in
{
  format = "1.0.0";
  attribute = "rocq-elpi";
  default-bundle = "rocq-9.2";
  bundles = {

    "rocq-9.1".rocqPackages = common-bundles // {
      rocq-core.override.version = "9.1";
      coq.override.version = "9.1";
      micromega-plugin.override.version = "master";  # to be removed at some point
      micromega-plugin.job = false;
      mathcomp-algebra-tactics.override.version = "master";
    };

    "rocq-9.2".rocqPackages = common-bundles // {
      rocq-core.override.version = "9.2";
      coq.override.version = "9.2";
      micromega-plugin.override.version = "master";  # to be removed at some point
      micromega-plugin.job = false;
      mathcomp-zify.job = false;  # not available yet
      jasmin.job = false;  # not available yet
    };

    "rocq-9.3".rocqPackages = common-bundles // {
      rocq-core.override.version = "9.3";
      coq.override.version = "9.3";
      micromega-plugin.override.version = "master";  # to be removed at some point
      micromega-plugin.job = false;
      mathcomp-zify.job = false;  # not available yet
      jasmin.job = false;  # not available yet
      coqeal.job = false;  # not available yet
      mathcomp-word.job = false;  # not available yet
      trakt.job = false;  # not available yet
    };

    "rocq-master".rocqPackages = common-bundles // {
      rocq-core.override.version = "master";
      coq.override.version = "master";
      micromega-plugin.override.version = "master";
      micromega-plugin.job = false;
      stdlib.override.version = "master";
      bignums.override.version = "master";
      jasmin.job = false;
    };

  } // optionalAttrs (min-elpi-version != default-elpi-version) {
    "rocq-master-min-elpi".rocqPackages = common-bundles // {
      rocq-elpi.override.elpi-version = min-elpi-version;
      rocq-core.override.version = "master";
      coq.override.version = "master";
      bignums.override.version = "master";
      stdlib.override.version = "master";
      jasmin.job = false;
    };
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.coq-elpi.authToken = "CACHIX_AUTH_TOKEN";

}
