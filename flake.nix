{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    grackle.url = "github:mjschwenne/grackle";
    self.submodules = true; # Use the submodule versions in the repo
    # Capture each submodule manually so we can export the commit hash
    # as a package to help keep transitive dependencies in sync
    coqutil = {
      url = "git+file:./external/coqutil";
      flake = false;
    };
    iris = {
      url = "git+file:./external/iris";
      flake = false;
    };
    iris-named-props = {
      url = "git+file:./external/iris-named-props";
      flake = false;
    };
    record-update = {
      url = "git+file:./external/record-update";
      flake = false;
    };
    stdpp = {
      url = "git+file:./external/stdpp";
      flake = false;
    };
  };

  outputs = {
    self,
    coqutil,
    iris,
    iris-named-props,
    record-update,
    stdpp,
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
        submodules = pkgs.writeText "perennial-submodules.json" ''
          {
            "perennial": "${
            if (self ? rev)
            then self.rev
            else self.dirtyRev
          }",
            "coqutil": "${
            if (coqutil ? rev)
            then coqutil.rev
            else coqutil.dirtyRev
          }",
            "iris": "${
            if (iris ? rev)
            then iris.rev
            else iris.dirtyRev
          }",
            "iris-named-props": "${
            if (iris-named-props ? rev)
            then iris-named-props.rev
            else iris-named-props.dirtyRev
          }",
            "record-update": "${
            if (record-update ? rev)
            then record-update.rev
            else record-update.dirtyRev
          }",
            "stdpp": "${
            if (stdpp ? rev)
            then stdpp.rev
            else stdpp.dirtyRev
          }"
          }
        '';
        perennial = pkgs.stdenv.mkDerivation {
          pname = "perennial";
          version = "unstable";

          src = ./.;

          nativeBuildInputs = with pkgs; [
            rocq-core
            rocqPackages.stdlib
          ];
          allowParrallelBuilds = true;

          buildPhase = ''
            make TIMED=false -j$NIX_BUILD_CORES
          '';
          installPhase = ''
            mkdir -p $out/lib/rocq/${pkgs.rocq-core.version}/user-contrib
            cp -r src $out/lib/rocq/${pkgs.rocq-core.version}/user-contrib/Perennial/
            cp -r new $out/lib/rocq/${pkgs.rocq-core.version}/user-contrib/New/
            cp -r external/Goose $out/lib/rocq/${pkgs.rocq-core.version}/user-contrib/Goose
          '';
        };
      in {
        packages = {
          inherit perennial submodules;
          default = perennial;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              rocq-core
              rocqPackages.stdlib

              go
              grackle.packages.${system}.default
              grackle.packages.${system}.goose
              protobuf

              # nix helpers
              nix-update
            ];

            shellHook = ''
              unset COQPATH
            '';
          };
      }
    );
}
