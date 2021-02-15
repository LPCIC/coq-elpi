{
  format = "1.0.0";
  coq-attribute = "coq-elpi";
  select = "coq-8.13";
  inputs."coq-8.13".coqPackages = {
    coq.override.version = "8.13";
  };
}
