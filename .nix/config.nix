{
  format = "1.0.0";
  attribute = "coq-elpi";
  default-bundle = "coq-master";
  bundles = {

    "coq-master".ocamlPackages.elpi.override.version = "v1.18.1";
    "coq-master".coqPackages = {
      coq.override.version = "master";
      
      hierarchy-builder.override.version = "master";

      mathcomp.override.version = "master";
      mathcomp.job = true;

      odd-order.override.version = "master";
      odd-order.job = true;

      mathcomp-classical.override.version = "master";
      mathcomp-classical.job = true;

      mathcomp-analysis.override.version = "master";
      mathcomp-analysis.job = true;

      mathcomp-finmap.override.version = "master";
      mathcomp-finmap.job = true;

      mathcomp-bigenough.override.version = "master";

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
