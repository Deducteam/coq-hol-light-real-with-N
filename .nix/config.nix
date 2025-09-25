{
  format = "1.0.0";
  attribute = "coq-hol-light-real-with-N";
  default-bundle = "default";
  bundles.default = {

    rocqPackages.rocq-core.override.version = "9.0";
    push-branches = [ "master" "nixReloaded" ];
  };
  ##  cachix.coq = {};
  ##  cachix.math-comp = {};
  ##  cachix.coq-community = {};
}
