{
  format = "1.0.0";
  attribute = "coq-elpi";
  default-bundle = "coq-8.18";
  bundles = {

    "coq-8.18".coqPackages = {
      hierarchy-builder.override.version = "master";
      coq.override.version = "8.18";
      hierarchy-builder-shim.job = false;

      mathcomp.override.version = "master";
      mathcomp.job = true;

      odd-order.override.version = "master";
      odd-order.job = true;

      mathcomp-analysis.override.version = "hierarchy-builder";
      mathcomp-analysis.job = true;

      mathcomp-finmap.override.version = "2.0.0";
      mathcomp-finmap.job = true;

      mathcomp-classical.override.version = "hierarchy-builder";
      mathcomp-classical.job = true;

      mathcomp-single-planB-src.job = false;
      mathcomp-single-planB.job = false;
      mathcomp-single.job = false;
    };

  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.coq-elpi.authToken = "CACHIX_AUTH_TOKEN";

}
