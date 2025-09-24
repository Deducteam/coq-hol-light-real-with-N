First steps are described in the README.md of the [Coq-nix-toolbox](https://github.com/rocq-community/coq-nix-toolbox/blob/master/README.md)

```bash
nix-shell https://github.com/coq-community/coq-nix-toolbox/archive/master.tar.gz --arg do-nothing true --run generateNixDefault
nix-shell --arg do-nothing true --run "initNixConfig coq-hol-light-real-with-N"
```
This generates the following files 
- default.nix : a file that describes the basic dependencies of the coq-nix-toolbix You canb keep as is (for the moment)
- .nix/coq-nix-toolbox.nix : with a hash number auto-generated
- .nix/config.nix : a skeleton with description of the package under devellopement as well as dependencies and reverse dependencies.

