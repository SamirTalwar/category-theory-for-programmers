{
  pkgs ? import <nixpkgs> { }
}:
pkgs.mkShell {
  name = "category-theory-for-programmers";

  buildInputs = [
    (pkgs.agda.withPackages(ps: [
      ps.standard-library
    ]))
  ];
}
