This Document describes how gihub pipeline actions were generated using the Coq nix toolbox.

The first steps are described in the README.md of the [Coq-nix-toolbox](https://github.com/rocq-community/coq-nix-toolbox/blob/master/README.md)

# Initializing Nix
First of all, initialize Nix (after installing) as follows :
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
    coqPackages.coq-core.override.version = "9.0";
    push-branches = [ "master" "nixReloaded" ];
  };
```
Once this field edited as described above, run `nix-shell` to check if every thing is ok.

# Generating the `coq-overlays` folder and the `default.nix` for `coq-hol-light-real-with-N`

Run `nix-shell --arg do-nothing true --run "createOverlay PACKAGENAME"` to generate 
`.nix/coq-overlays/coq-hol-light-real-with-N/default.nix` then edit this file as follows :
```nix
{ pkgs ? import <nixpkgs> {}
  , lib, mkCoqDerivation, which, coq
  , bignums <!-- Coq-hol-light-real-with-N  depends on bignums  -->
  , version ? null }:

with lib; mkCoqDerivation {
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
This file tells Nix how to build the `coq-hol-light-real-with-N` package including where to find the sources and package dependencies.

# Creating the `default.nix` file of the reverse dependency
The objective being to test the reverse dependency of `coq-hol-light-real-with-N`, name `coq-hol-light`, we will create a folder dedicated to this package and explain how to build it from its dependencies.
```
mkdir .nix/coq-overlays/coq-hol-light
touch .nix/coq-overlays/coq-hol-light/default.nix
```
then edit it as follows :
```
{ lib, mkCoqDerivation, coq-hol-light-real-with-N
  , fourcolor
  , stdlib
  , version ? null }:
with lib; mkCoqDerivation {
  pname = "coq-hol-light";
#  inherit version;
  repo = "coq-hol-light";
  owner = "Deducteam";
  domain = "github.com";
  version = "Deducteam:main";
#  release = {
#    "3.0.0".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
#  };
#  releaseRev = v: "v${v}";
  propagatedBuildInputs = [ coq-hol-light-real-with-N
    stdlib
    fourcolor
  ];
  meta = {
  };
}
```
This file notably tell Nix where to find the sources of `coq-hol-light` and that `coq-hol-light` depends on `coq-hol-light-real-with-N` which will have as side effect that the `coq-hol-light` job in the pipeline (that we will create in a moment) will be triggered right after the `coq-hol-light-real-with-N` job.

# Testing build are OK
Before testing the builds in the github pipeline, it can be usefull to test them locally.
To this end run
```
nix-build
```
to test `coq-hol-light-real-with-N`
and run 
```
nix-build --argstr job coq-hol-light
```
to test `coq-hol-light`

If no errors are detected, one can move to the next step.

# Generating the github actions
To generate the github actions, simply run 
```
nix-shell --arg do-nothing true --run "genNixActions"
```
This will generate `.github/workflows/nix-action-default.yml`. This file contains three jobs : a job to build Coq, another to build `coq-hol-light-real-with-N` and the last to generate `coq-hol-light`.

If everything goes well, one will see the following pipeline when you push the new code.

