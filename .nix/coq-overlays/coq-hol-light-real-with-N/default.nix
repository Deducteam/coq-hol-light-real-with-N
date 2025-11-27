{ pkgs ? import <nixpkgs> {}
  , lib, mkCoqDerivation, which, coq
  , stdlib
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
