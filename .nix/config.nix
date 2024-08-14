let common-bundles = {
  hierarchy-builder.override.version = "master";
  hierarchy-builder-shim.job = false;
  mathcomp.override.version = "master";
  odd-order.override.version = "master";
  mathcomp-analysis.override.version = "master";
  mathcomp-finmap.override.version = "master";
  mathcomp-classical.override.version = "master";

  mathcomp-single-planB-src.job = false;
  mathcomp-single-planB.job = false;
  mathcomp-single.job = false;

  deriving.job = false;
  reglang.job = false;
}; in
{
  format = "1.0.0";
  attribute = "coq-elpi";
  default-bundle = "coq-8.19";
  bundles = {

    "coq-8.19".coqPackages = common-bundles // {
      coq.override.version = "8.19";
    };

    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "master";
    };
      
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.coq-elpi.authToken = "CACHIX_AUTH_TOKEN";

}
