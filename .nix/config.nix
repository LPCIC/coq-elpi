{
  format = "1.0.0";
  attribute = "coq-elpi";
  default-bundle = "coq-8.17";
  bundles = {

    "coq-8.17".coqPackages = {
      coq.override.version = "8.17";
      hierarchy-builder.override.version = "master";
      hierarchy-builder-shim.job = false;
      mathcomp.override.version = "master";
      mathcomp.job = true;
      odd-order.override.version = "master";
      odd-order.job = true;
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
