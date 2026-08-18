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
        # rocq-stdlib is the only store path that holds a complete Rocq prefix:
        # opam-nix copies rocq-core's Corelib and Ltac2 into it and then installs
        # Stdlib alongside. rocq-stdlib's setup hook exports ROCQLIB accordingly,
        # but rocq-core is one of its propagated inputs and unconditionally
        # re-exports ROCQLIB to its *own* prefix, which has Corelib and Ltac2 but
        # no Stdlib. Since these opam-nix derivations list their dependencies in
        # both nativeBuildInputs and buildInputs, rocq-core's hook is activated
        # last and wins, and every `Require Import List` then fails with
        # "Unable to locate library List". Re-export ROCQLIB from a build phase,
        # which runs after all setup hooks, so it cannot be clobbered again.
        rocqLibOf = rocqStdlib: ocamlVersion: "${rocqStdlib}/lib/ocaml/${ocamlVersion}/site-lib/coq";
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
                rocqLib = rocqLibOf prev.rocq-stdlib prev.ocaml.version;
                addRocqHook =
                  pkg:
                  pkg.overrideAttrs (old: {
                    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ rocqHook ];
                    preConfigure = (old.preConfigure or "") + ''
                      export ROCQLIB="${rocqLib}"
                    '';
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
        # The ROCQLIB that actually contains Stdlib; see rocqLibOf above.
        rocqLib = rocqLibOf perennialPkgs'.rocq-stdlib perennialPkgs'.ocaml.version;
        perennial = perennialPkgs'.perennial.overrideAttrs (
          finalAttrs: previousAttrs: {
            nativeBuildInputs = with pkgs; [ python3 ] ++ previousAttrs.nativeBuildInputs;
            preBuild = ''
              export ROCQLIB="${rocqLib}"
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
              export ROCQLIB="${rocqLib}"
              # swap ROCQPATH for COQPATH
              export ROCQPATH=$COQPATH
              unset COQPATH
            '';
          };
      }
    );
}
