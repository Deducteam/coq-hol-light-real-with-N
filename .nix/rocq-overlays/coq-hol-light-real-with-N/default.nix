{ lib, mkRocqDerivation, which, coq
  , bignums
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
