{ rustPlatform, libbap, clang }:
with rustPlatform;

buildRustPackage rec {
  name = "bap-rust";
  src  = ./.;
  buildInputs = [ libbap clang ];
  propagatedBuildInputs = [ libbap ]; # Rust links at the end
  depsSha256 = "";
}
