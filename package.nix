{ rustPlatform, libbap, clang }:
with rustPlatform;

buildRustPackage rec {
  name = "bap-rust";
  src  = ./.;
  buildInputs = [ libbap clang ];
  depsSha256 = "";
}
