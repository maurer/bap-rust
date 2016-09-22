{ pkgs ? (import ../nixpkgs {}).pkgs }:

with pkgs;

callPackage ./package.nix { }
