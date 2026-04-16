{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    grackle.url = "github:mjschwenne/grackle";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-rocq-repo = {
      url = "github:rocq-prover/opam";
      flake = false;
    };
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.opam-repository.follows = "opam-repository";
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      grackle,
      opam-nix,
      opam-repository,
      opam-rocq-repo,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        inherit (opam-nix.lib.${system}) buildOpamProject;
        # Replicate the rocq-prover setup hook from opam-nix's default overlay.
        # This hook is normally applied to the rocq-prover package, but perennial
        # depends on rocq-runtime directly (not rocq-prover), so the hook never
        # fires. We add it to each Rocq package via overrideScope instead.
        #
        # The hook does two things:
        # 1. addCoqPath: env hook that adds lib/coq/<ver>/user-contrib to COQPATH
        #    for each dependency, so dependent builds can find installed .vo files.
        # 2. COQLIBINSTALL: points make install at $out instead of the read-only
        #    rocq-stdlib store path.
        mkRocqHook =
          rocqVersion: ocamlVersion:
          pkgs.makeSetupHook { name = "rocq-path-hook"; } (
            pkgs.writeText "rocq-path-hook.sh" ''
              addCoqPath () {
                if test -d "$1/lib/coq/${rocqVersion}/user-contrib"; then
                  export COQPATH="''${COQPATH-}''${COQPATH:+:}$1/lib/coq/${rocqVersion}/user-contrib/"
                fi
              }

              addEnvHooks "$targetOffset" addCoqPath

              export DESTDIR="$out/lib/coq/${rocqVersion}"
              export COQLIBINSTALL="$out/lib/coq/${rocqVersion}/user-contrib"
              export COQPLUGININSTALL="$out/lib/ocaml/${ocamlVersion}/site-lib"
              export COQUSERCONTRIB="$out/lib/coq/${rocqVersion}/user-contrib"
            ''
          );
        perennialPkgs' =
          (buildOpamProject {
            repos = [
              "${opam-repository}"
              "${opam-rocq-repo}/released"
            ];
            pinDepends = true;
            resolveArgs.dev = true;
          } "perennial" ./. { }).overrideScope
            (
              final: prev:
              let
                rocqHook = mkRocqHook prev.rocq-runtime.version prev.ocaml.version;
                addRocqHook =
                  pkg:
                  pkg.overrideAttrs (old: {
                    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ rocqHook ];
                  });
              in
              {
                coq-coqutil = addRocqHook prev.coq-coqutil;
                coq-record-update = addRocqHook prev.coq-record-update;
                rocq-stdpp = addRocqHook prev.rocq-stdpp;
                rocq-iris = addRocqHook prev.rocq-iris;
                iris-named-props = addRocqHook prev.iris-named-props;
              }
            );
        perennial = perennialPkgs'.perennial.overrideAttrs (
          finalAttrs: previousAttrs: {
            nativeBuildInputs = with pkgs; [ python3 ] ++ previousAttrs.nativeBuildInputs;
            preBuild = ''
              # swap ROCQPATH for COQPATH, avoiding overriding the complex configurationPhase
              export ROCQPATH=$COQPATH
              unset COQPATH
            '';
            buildPhase = ''
              runHook preBuild
              make -j$NIX_BUILD_CORES all
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              ./etc/install.sh all
              runHook postInstall
            '';
          }
        );
        # remove the perennial package from perennialPkgs since it won't build without python
        perennialPkgs = removeAttrs perennialPkgs' [ "perennial" ];
      in
      {
        packages = {
          inherit perennialPkgs perennial;
          default = perennial;
        };
        devShells.default =
          with pkgs;
          mkShell {
            buildInputs = [
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
            ++ (with perennialPkgs; [
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
