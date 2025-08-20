{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    grackle.url = "github:mjschwenne/grackle";
    self.submodules = true;
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
        rocq = pkgs.rocq-core;
        rocq-std = pkgs.rocqPackages.stdlib;
        rocqv = rocq.rocq-version;
        perennial = pkgs.stdenv.mkDerivation {
          pname = "perennial";
          version = "unstable-rocq${rocqv}";

          src = ./.;

          nativeBuildInputs = [
            rocq
            rocq-std
          ];
          allowParrallelBuilds = true;

          buildPhase = ''
            make TIMED=false -j$NIX_BUILD_CORES
          '';
          # Install perennial AND all it's dependencies to ensure the correct version,
          # down to the commit hash, is installed
          installPhase = ''
            mkdir -p $out/lib/coq/${rocqv}/user-contrib

            cp -r src $out/lib/coq/${rocqv}/user-contrib/Perennial/
            cp -r new $out/lib/coq/${rocqv}/user-contrib/New/
            cp -r external/Goose $out/lib/coq/${rocqv}/user-contrib/

            cp -r external/coqutil/src/coqutil $out/lib/coq/${rocqv}/user-contrib/
            cp -r external/iris/iris $out/lib/coq/${rocqv}/user-contrib/
            cp -r external/iris/iris_deprecated $out/lib/coq/${rocqv}/user-contrib/iris/deprecated
            cp -r external/iris/iris_heap_lang $out/lib/coq/${rocqv}/user-contrib/iris/heap_lang
            cp -r external/iris/iris_unstable $out/lib/coq/${rocqv}/user-contrib/iris/unstable
            cp -r external/iris-named-props/src $out/lib/coq/${rocqv}/user-contrib/iris_named_props
            cp -r external/record-update/src $out/lib/coq/${rocqv}/user-contrib/record-update
            cp -r external/stdpp/stdpp $out/lib/coq/${rocqv}/user-contrib/
            cp -r external/stdpp/stdpp_unstable $out/lib/coq/${rocqv}/user-contrib/stdpp/unstable
            cp -r external/stdpp/stdpp_bitvector $out/lib/coq/${rocqv}/user-contrib/stdpp/bitvector
          '';
        };
      in {
        packages = {
          inherit perennial;
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
