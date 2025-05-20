{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    grackle.url = "github:mjschwenne/grackle";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    grackle,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
      in {
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              coq
              coqPackages.stdlib

              go
              grackle.packages.${system}.default
              grackle.packages.${system}.goose
              protobuf

              # nix helpers
              nix-prefetch-git
              nix-prefetch-github
              nix-prefetch
            ];

            shellHook = ''
              unset COQPATH
            '';
          };
      }
    );
}
