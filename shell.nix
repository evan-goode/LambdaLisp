{ pkgs ? import <nixos-unstable> {}}:
  pkgs.mkShell {
    nativeBuildInputs = let
      env = pyPkgs : with pyPkgs; [
        poetry
      ];
    in with pkgs; [
      (python310.withPackages env)
    ];
}
