{
  format = "1.0.0";
  attribute = "coq-hol-light-real-with-N";
  default-bundle = "default";
  bundles.default = {
    coqPackages.coq-hol-light.override.version = "3.0.0";
    coqPackages.rocq-core.override.version = "9.0";
    push-branches = [ "**" ];
  };
  cachix.coq = {};
  ##  cachix.math-comp = {};
  ##  cachix.coq-community = {};
}
