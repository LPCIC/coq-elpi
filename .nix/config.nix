{
  format = "1.0.0";
  attribute = "coq-elpi";
  default-bundle = "coq-8.16";
  bundles = {

    "coq-8.16".coqPackages = {
      coq.override.version = "8.16";
      hierarchy-builder.override.version = "master";
      mathcomp.override.version = "hierarchy-builder";
      mathcomp.job = true;
      odd-order.override.version = "hirarchy-builder";
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
