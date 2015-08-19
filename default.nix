{ pkgs ? (import <local> {}).pkgs }:

with pkgs;

callPackage (import ./package.nix) { }
