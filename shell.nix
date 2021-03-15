{ pkgs ? import <nixpkgs> { } }:
let
  agda = ((pkgs.agda).withPackages (ps: [
    ps.standard-library
  ]));
  ghc = pkgs.ghc.withPackages (ps: [
    ps.random
  ]);
in
pkgs.mkShell
{
  name = "category-theory-for-programmers";

  buildInputs = [
    agda
    ghc
  ];
}
