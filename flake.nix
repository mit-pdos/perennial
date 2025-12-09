{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/f61125a668a320878494449750330ca58b78c557";
    flake-utils.url = "github:numtide/flake-utils";
    grackle.url = "github:mjschwenne/grackle";
    opam-nix.url = "github:tweag/opam-nix";
    opam-repository.url = "github:ocaml/opam-repository";
    opam-repository.flake = false;
  };

  outputs = {
    nixpkgs,
    flake-utils,
    grackle,
    opam-nix,
    opam-repository,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        opam-rocq-repo = pkgs.fetchFromGitHub {
          owner = "rocq-prover";
          repo = "opam";
          rev = "21386fecc599280c73801a6a270111a1fabca62b";
          hash = "sha256-AeSR497sH7JftvtGPpRZzfaJ/L7asuL/hlaaMZDx7/k=";
        };
        inherit
          (opam-nix.lib.${system}.buildOpamProject {
              repos = ["${opam-repository}" "${opam-rocq-repo}/released"];
            } "perennial"
            ./. {})
          perennial
          ;
        perennial-final = perennial.overrideAttrs (finalAttrs: previousAttrs: {
          nativeBuildInputs = with pkgs; [python3] ++ previousAttrs.nativeBuildInputs;
        });
      in {
        packages = {
          inherit perennial-final;
          default = perennial-final;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              opam

              go
              grackle.packages.${system}.default
              grackle.packages.${system}.goose
              protobuf

              # nix helpers
              nix-update

              # opam related system dependencies
              pkg-config
              gmp
              findutils
            ];

            shellHook = ''
              unset COQPATH
              eval $(opam env)
            '';
          };
      }
    );
}
