{
  format = "1.0.0";

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  attribute = "coq-elpi";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "default";

  ## write one `bundles.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well
  bundles.default = {

  coqPackages.coq.override.version = "8.13";

  ## In some cases, light overrides are not available/enough
  ## in which case you can use either
  # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
  ## or a "long" overlay to put in `.nix/coq-overlays
  ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
  ## to automatically retrieve the one from nixpkgs
  ## if it exists and is correctly named/located

  ## You can override Coq and other Coq coqPackages
  ## throught the following attribute
  ## If <ocaml-pkg> does not support lights overrides,
  ## you may use `overrideAttrs` or long overlays
  ## located in `.nix/ocaml-overlays`
  ## (there is no automation for this one)
  #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

  ## You can also override packages from the nixpkgs toplevel
  # <nix-pkg>.override.overrideAttrs = o: <overrides>;
  ## Or put an overlay in `.nix/overlays`

  ## you may mark a package as a CI job as follows
  #  coqPackages.<another-pkg>.ci.job = "test";
  ## It can then be built throught
  ## nix-build --argstr ci "default" --arg ci-job "test";

  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  
  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  
  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"
  
  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
