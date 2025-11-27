This Document describes how Gihub pipeline actions were generated using the Coq-nix-toolbox.

The first steps are described in the README.md of the [Coq-nix-toolbox](https://github.com/rocq-community/coq-nix-toolbox/blob/master/README.md)

# Installing Nix
Nix installation can be done in Multi-user mode with
```bash
sh <(curl --proto '=https' --tlsv1.2 -L https://nixos.org/nix/install) --daemon
```
or in Single-user mode :
```bash
sh <(curl --proto '=https' --tlsv1.2 -L https://nixos.org/nix/install) --no-daemon
```
Details on the pros and cons of both methods can be found on the [Nix installation webpage](https://nixos.org/download/)

# Initializing Nix
First, initialize Nix as follows :
```bash
nix-shell https://github.com/coq-community/coq-nix-toolbox/archive/master.tar.gz --arg do-nothing true --run generateNixDefault
nix-shell --arg do-nothing true --run "initNixConfig coq-hol-light-real-with-N"
```
This generates the following files 
- `default.nix` : a file that describes the basic dependencies of the `coq-nix-toolbix` that you can keep as is (for the moment)
- `.nix/coq-nix-toolbox.nix` : with a hash number auto-generated
- `.nix/config.nix` : a skeleton with description of the package under development as well as dependencies and reverse dependencies.

# Editing the config.nix file
In the `.nix/config.nix` file one needs to edit the following fields in particular :
```
  attribute = "coq-hol-light-real-with-N";
  default-bundle = "default";
  bundles.default = {
    coqPackages.coq-core.override.version = "9.0";
    push-branches = [ "**" ];
  };
```
Then, run `nix-shell` to check if every thing is ok.

# Generating the `coq-overlays` folder and the `default.nix` for `coq-hol-light-real-with-N`

Run `nix-shell --arg do-nothing true --run "createOverlay coq-hol-light-real-with-N"` to generate 
`.nix/coq-overlays/coq-hol-light-real-with-N/default.nix` then edit this file as follows :
```nix
{ pkgs ? import <nixpkgs> {}
  , lib, mkCoqDerivation, which, coq
  ,   , stdlib <!-- Coq-hol-light-real-with-N  depends on stdlib  -->
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "coq-hol-light-real-with-N";
  repo = "coq-hol-light-real-with-N";
  owner = "Deducteam";
  domain = "github.com";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;
  buildInputs = [ stdlib ];
  meta = {
  };
}
```
This file tells Nix how to build the `coq-hol-light-real-with-N` package including where to find the sources and package dependencies.

# Adding the reverse dependency to coq-hol-light
A reverse dependency is a package that you want to test every time the current library is changed (specifically, when pushes are made to the branches defined in `.nix/config.nix`).
This is achieved thanks to the generation of a job in the pipeline that dependents on the one that builds the current library.

In our particular case, the objective is to test the `coq-hol-light` library when `coq-hol-light-real-with-N` is updated. To this end, we will create a folder dedicated to this package and explain how to build it from its dependencies.
```bash
mkdir .nix/coq-overlays/coq-hol-light
touch .nix/coq-overlays/coq-hol-light/default.nix
```
Then edit it as follows :
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
This file notably tells `Nix` where to find the sources of `coq-hol-light` and that `coq-hol-light` depends on `coq-hol-light-real-with-N` which will have as side effect that the `coq-hol-light` job in the pipeline (that we will create in a moment) will be triggered right after the `coq-hol-light-real-with-N` job.

## Adding more reverse dependencies
To add more reverse dependencies, first check whether the package of the reverse dependency already has a `Nix` package in the [Nix packages GitHub repo](https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules).

If the package does not exist, just repeat the steps describe above for `coq-hol-light`.

Otherwise, simply run `nix-shell --arg do-nothing true --run "fetchCoqOverlay <RevDepPackagename>"` to generate the corresponding `default.nix` under `.nix/coq-overlays/<RevDepPackagename>/` and add a dependency to `coq-hol-light-real-with-N` as described above for `coq-hol-light`.

For illustration, the following describes how to add a reverse dependencies to a package named `MenhirLib`
```bash
nix-shell --arg do-nothing true --run "fetchCoqOverlay MenhirLib"
```
the edit `nix/coq-overlays/MenhirLib/default.nix` as follows
```
{
  lib,
  mkCoqDerivation,
  coq,
  stdlib,
  coq-hol-light-real-with-N,
  version ? null,
}:
....
    propagatedBuildInputs = [ stdlib coq-hol-light-real-with-N ];
....
```
# Testing builds are OK
Before testing the builds in the GitHub pipeline, it can be useful to test them locally.

To this end run `nix-build` to test `coq-hol-light-real-with-N` and `nix-build --argstr job coq-hol-light` to test `coq-hol-light`.

If no errors are detected, one can move to the next step.

# Generating the GitHub actions
To generate the GitHub actions, simply run 
```bash
nix-shell --arg do-nothing true --run "genNixActions"
```
This will generate `.github/workflows/nix-action-default.yml`. This file contains three jobs : a job to build `Rocq`, another to build `coq-hol-light-real-with-N` and the last to generate `coq-hol-light`.

If everything goes well, one will see the following pipeline when you push the new code.

Optionally, to avoid triggering the pipeline when `.md` files are changed, one can add the following lines to the end of the `.github/workflows/nix-action-default.yml` generated file under section `on.push` :
```yml
on
...
  push
  ...
    paths-ignore:
    - '**/*.md'
```

