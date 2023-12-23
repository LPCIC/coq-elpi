{
  format = "1.0.0";
  attribute = "coq-elpi";
  default-bundle = "coq-8.19";
  bundles = {

    "coq-8.19".coqPackages = {
      coq.override.version = "8.19+rc1";
      
      hierarchy-builder.override.version = "coq-elpi-2";
      hierarchy-builder-shim.job = false;

      coq-elpi.override.version = "master";

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
