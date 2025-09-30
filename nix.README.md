First steps are described in the README.md of the [Coq-nix-toolbox](https://github.com/rocq-community/coq-nix-toolbox/blob/master/README.md)

```bash
nix-shell https://github.com/coq-community/coq-nix-toolbox/archive/master.tar.gz --arg do-nothing true --run generateNixDefault
nix-shell --arg do-nothing true --run "initNixConfig coq-hol-light-real-with-N"
```
This generates the following files 
- default.nix : a file that describes the basic dependencies of the coq-nix-toolbix You can keep as is (for the moment)
- .nix/coq-nix-toolbox.nix : with a hash number auto-generated
- .nix/config.nix : a skeleton with description of the package under devellopement as well as dependencies and reverse dependencies.

# Editing the config.nix file
In the `.nix/config.nix` file one needs to edit the following informations in particular :
```
  attribute = "coq-hol-light-real-with-N";
  default-bundle = "default";
  bundles.default = {
    rocqPackages.rocq-core.override.version = "9.0";
    push-branches = [ "master" "nixReloaded" ];
  };
```
Once this field edited as described above, run nix-shell to check if every thing is ok.

# Generating the Rocq-overlays folder and the default.nix for coq-hol-light-real-with

Run `nix-shell --arg do-nothing true --run "createOverlay PACKAGENAME"` to generate 
`.nix/rocq-overlays/coq-hol-light-real-with-N/default.nix` then edit this file as follows :
```
{ lib, mkRocqDerivation, which, coq, bignums <!-- add bignums as a dependency of Coq-hol-light-real-with-N  -->
  , version ? null }:

with lib; mkRocqDerivation {
  pname = "coq-hol-light-real-with-N";
  repo = "coq-hol-light-real-with-N";
  owner = "Deducteam";
  domain = "github.com";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;
  buildInputs = [ bignums ];
  meta = {
  };
}

```
