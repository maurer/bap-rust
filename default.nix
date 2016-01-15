{ pkgs ? (import <local> {}).pkgs }:

with pkgs;

lib.allCall (import ./package.nix) { }
