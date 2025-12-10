{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/f61125a668a320878494449750330ca58b78c557";
    flake-utils.url = "github:numtide/flake-utils";
    grackle.url = "github:mjschwenne/grackle";
    opam-nix.url = "github:tweag/opam-nix";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-rocq-repo = {
      url = "github:rocq-prover/opam";
      flake = false;
    };
  };

  outputs = {
    nixpkgs,
    flake-utils,
    grackle,
    opam-nix,
    opam-repository,
    opam-rocq-repo,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        inherit (opam-nix.lib.${system}) buildOpamProject;
        perennialPkgs' =
          buildOpamProject {
            repos = ["${opam-repository}" "${opam-rocq-repo}/released"];
          } "perennial"
          ./. {};
        perennial = perennialPkgs'.perennial.overrideAttrs (finalAttrs: previousAttrs: {
          nativeBuildInputs = with pkgs; [python3] ++ previousAttrs.nativeBuildInputs;
          preBuild = ''
            # swap ROCQPATH for COQPATH, avoiding overriding the complex configurationPhase
            export ROCQPATH=$COQPATH
            unset COQPATH
          '';
        });
        # remove the perennial package from perennialPkgs since it won't build without python
        perennialPkgs = removeAttrs perennialPkgs' ["perennial"];
      in {
        packages = {
          inherit perennialPkgs perennial;
          default = perennial;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
                opam
                python3

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
              ]
              ++ (with perennialPkgs'; [
                rocq-runtime
                rocq-stdlib
                coq-coqutil
                coq-record-update
                rocq-stdpp
                rocq-iris
                iris-named-props
              ]);

            shellHook = ''
              # swap ROCQPATH for COQPATH
              export ROCQPATH=$COQPATH
              unset COQPATH
            '';
          };
      }
    );
}
